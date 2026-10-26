import V185TrunkScan23Chunk0920

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5451127 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_5451127 : Nat := 118140960795 + 5451127 * 2 ^ 59
def prefixEnd_5451127 : Nat := 4983230072969 + 3 ^ 40 * 5451127 * 2
def baseEnd_5451127 : Nat := 2799048259701399174243229

theorem tailTrace_5451127 : CollatzResearch.WordTrace tailWord_5451127 prefixEnd_5451127 2799048259701399174243229 := by
  unfold tailWord_5451127
  simp only [CollatzResearch.WordTrace]
  refine ⟨198818935322505332217735635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132545956881670221478490423 198818935322505332217735635)
  ·
    refine ⟨298228402983757998326603453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198818935322505332217735635 298228402983757998326603453)
    ·
      refine ⟨111835651118909249372476295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298228402983757998326603453 111835651118909249372476295)
      ·
        refine ⟨167753476678363874058714443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111835651118909249372476295 167753476678363874058714443)
        ·
          refine ⟨251630215017545811088071665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167753476678363874058714443 251630215017545811088071665)
          ·
            refine ⟨188722661263159358316053749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251630215017545811088071665 188722661263159358316053749)
            ·
              refine ⟨17692749493421189842130039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188722661263159358316053749 17692749493421189842130039)
              ·
                refine ⟨26539124240131784763195059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17692749493421189842130039 26539124240131784763195059)
                ·
                  refine ⟨39808686360197677144792589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26539124240131784763195059 39808686360197677144792589)
                  ·
                    refine ⟨14928257385074128929297221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39808686360197677144792589 14928257385074128929297221)
                    ·
                      refine ⟨2799048259701399174243229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14928257385074128929297221 2799048259701399174243229)
                      ·
                        rfl

theorem cell23_5451127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_5451127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451127 prefixEnd_5451127 := by exact prefixLift 5451127
  have htrace : WordTrace (prefixWord ++ tailWord_5451127) baseStart_5451127 baseEnd_5451127 := by
    simpa [prefixWord, tailWord_5451127, baseEnd_5451127] using wordTrace_append hprefix tailTrace_5451127
  have hstable : (prefixWord ++ tailWord_5451127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451127).length < 2 ^ (prefixWord ++ tailWord_5451127).sum := by decide
  have hdescent : baseEnd_5451127 < baseStart_5451127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451181 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5451181 : Nat := 118140960795 + 5451181 * 2 ^ 59
def prefixEnd_5451181 : Nat := 4983230072969 + 3 ^ 40 * 5451181 * 2
def baseEnd_5451181 : Nat := 2799075987656741962967981

theorem tailTrace_5451181 : CollatzResearch.WordTrace tailWord_5451181 prefixEnd_5451181 2799075987656741962967981 := by
  unfold tailWord_5451181
  simp only [CollatzResearch.WordTrace]
  refine ⟨198820904864309699440201397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132547269909539799626800931 198820904864309699440201397)
  ·
    refine ⟨18639459831029034322518881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198820904864309699440201397 18639459831029034322518881)
    ·
      refine ⟨13979594873271775741889161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18639459831029034322518881 13979594873271775741889161)
      ·
        refine ⟨10484696154953831806416871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13979594873271775741889161 10484696154953831806416871)
        ·
          refine ⟨15727044232430747709625307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10484696154953831806416871 15727044232430747709625307)
          ·
            refine ⟨23590566348646121564437961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15727044232430747709625307 23590566348646121564437961)
            ·
              refine ⟨17692924761484591173328471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23590566348646121564437961 17692924761484591173328471)
              ·
                refine ⟨26539387142226886759992707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17692924761484591173328471 26539387142226886759992707)
                ·
                  refine ⟨39809080713340330139989061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26539387142226886759992707 39809080713340330139989061)
                  ·
                    refine ⟨7464202633751311901247949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39809080713340330139989061 7464202633751311901247949)
                    ·
                      refine ⟨2799075987656741962967981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464202633751311901247949 2799075987656741962967981)
                      ·
                        rfl

theorem cell23_5451181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5451181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451181 prefixEnd_5451181 := by exact prefixLift 5451181
  have htrace : WordTrace (prefixWord ++ tailWord_5451181) baseStart_5451181 baseEnd_5451181 := by
    simpa [prefixWord, tailWord_5451181, baseEnd_5451181] using wordTrace_append hprefix tailTrace_5451181
  have hstable : (prefixWord ++ tailWord_5451181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451181).length < 2 ^ (prefixWord ++ tailWord_5451181).sum := by decide
  have hdescent : baseEnd_5451181 < baseStart_5451181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451211 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 3]
def baseStart_5451211 : Nat := 118140960795 + 5451211 * 2 ^ 59
def prefixEnd_5451211 : Nat := 4983230072969 + 3 ^ 40 * 5451211 * 2
def baseEnd_5451211 : Nat := 2799091392076376845592843

theorem tailTrace_5451211 : CollatzResearch.WordTrace tailWord_5451211 prefixEnd_5451211 2799091392076376845592843 := by
  unfold tailWord_5451211
  simp only [CollatzResearch.WordTrace]
  refine ⟨198821999054201014563793487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132547999369467343042528991 198821999054201014563793487)
  ·
    refine ⟨298232998581301521845690231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198821999054201014563793487 298232998581301521845690231)
    ·
      refine ⟨447349497871952282768535347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298232998581301521845690231 447349497871952282768535347)
      ·
        refine ⟨671024246807928424152803021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447349497871952282768535347 671024246807928424152803021)
        ·
          refine ⟨251634092552973159057301133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 671024246807928424152803021 251634092552973159057301133)
          ·
            refine ⟨94362784707364934646487925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251634092552973159057301133 94362784707364934646487925)
            ·
              refine ⟨8846511066315462623108243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94362784707364934646487925 8846511066315462623108243)
              ·
                refine ⟨13269766599473193934662365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8846511066315462623108243 13269766599473193934662365)
                ·
                  refine ⟨4976162474802447725498387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13269766599473193934662365 4976162474802447725498387)
                  ·
                    refine ⟨7464243712203671588247581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976162474802447725498387 7464243712203671588247581)
                    ·
                      refine ⟨2799091392076376845592843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464243712203671588247581 2799091392076376845592843)
                      ·
                        rfl

theorem cell23_5451211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 3].length) (baseStart_5451211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451211 prefixEnd_5451211 := by exact prefixLift 5451211
  have htrace : WordTrace (prefixWord ++ tailWord_5451211) baseStart_5451211 baseEnd_5451211 := by
    simpa [prefixWord, tailWord_5451211, baseEnd_5451211] using wordTrace_append hprefix tailTrace_5451211
  have hstable : (prefixWord ++ tailWord_5451211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451211).length < 2 ^ (prefixWord ++ tailWord_5451211).sum := by decide
  have hdescent : baseEnd_5451211 < baseStart_5451211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451217 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_5451217 : Nat := 118140960795 + 5451217 * 2 ^ 59
def prefixEnd_5451217 : Nat := 4983230072969 + 3 ^ 40 * 5451217 * 2
def baseEnd_5451217 : Nat := 2799094472960303822117815

theorem tailTrace_5451217 : CollatzResearch.WordTrace tailWord_5451217 prefixEnd_5451217 2799094472960303822117815 := by
  unfold tailWord_5451217
  simp only [CollatzResearch.WordTrace]
  refine ⟨198822217892179277588511905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132548145261452851725674603 198822217892179277588511905)
  ·
    refine ⟨149116663419134458191383929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198822217892179277588511905 149116663419134458191383929)
    ·
      refine ⟨111837497564350843643537947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149116663419134458191383929 111837497564350843643537947)
      ·
        refine ⟨167756246346526265465306921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111837497564350843643537947 167756246346526265465306921)
        ·
          refine ⟨125817184759894699098980191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167756246346526265465306921 125817184759894699098980191)
          ·
            refine ⟨188725777139842048648470287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125817184759894699098980191 188725777139842048648470287)
            ·
              refine ⟨283088665709763072972705431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188725777139842048648470287 283088665709763072972705431)
              ·
                refine ⟨424632998564644609459058147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283088665709763072972705431 424632998564644609459058147)
                ·
                  refine ⟨636949497846966914188587221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424632998564644609459058147 636949497846966914188587221)
                  ·
                    refine ⟨14928503855788287051295013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 636949497846966914188587221 14928503855788287051295013)
                    ·
                      refine ⟨2799094472960303822117815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14928503855788287051295013 2799094472960303822117815)
                      ·
                        rfl

theorem cell23_5451217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_5451217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451217 prefixEnd_5451217 := by exact prefixLift 5451217
  have htrace : WordTrace (prefixWord ++ tailWord_5451217) baseStart_5451217 baseEnd_5451217 := by
    simpa [prefixWord, tailWord_5451217, baseEnd_5451217] using wordTrace_append hprefix tailTrace_5451217
  have hstable : (prefixWord ++ tailWord_5451217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451217).length < 2 ^ (prefixWord ++ tailWord_5451217).sum := by decide
  have hdescent : baseEnd_5451217 < baseStart_5451217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451221 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_5451221 : Nat := 118140960795 + 5451221 * 2 ^ 59
def prefixEnd_5451221 : Nat := 4983230072969 + 3 ^ 40 * 5451221 * 2
def baseEnd_5451221 : Nat := 2799096526882921806467797

theorem tailTrace_5451221 : CollatzResearch.WordTrace tailWord_5451221 prefixEnd_5451221 2799096526882921806467797 := by
  unfold tailWord_5451221
  simp only [CollatzResearch.WordTrace]
  refine ⟨198822363784164786271657517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132548242522776524181105011 198822363784164786271657517)
  ·
    refine ⟨74558386419061794851871569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198822363784164786271657517 74558386419061794851871569)
    ·
      refine ⟨55918789814296346138903677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74558386419061794851871569 55918789814296346138903677)
      ·
        refine ⟨20969546180361129802088879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55918789814296346138903677 20969546180361129802088879)
        ·
          refine ⟨31454319270541694703133319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20969546180361129802088879 31454319270541694703133319)
          ·
            refine ⟨47181478905812542054699979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31454319270541694703133319 47181478905812542054699979)
            ·
              refine ⟨70772218358718813082049969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47181478905812542054699979 70772218358718813082049969)
              ·
                refine ⟨53079163769039109811537477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70772218358718813082049969 53079163769039109811537477)
                ·
                  refine ⟨9952343206694833089663277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53079163769039109811537477 9952343206694833089663277)
                  ·
                    refine ⟨3732128702510562408623729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9952343206694833089663277 3732128702510562408623729)
                    ·
                      refine ⟨2799096526882921806467797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732128702510562408623729 2799096526882921806467797)
                      ·
                        rfl

theorem cell23_5451221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_5451221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451221 prefixEnd_5451221 := by exact prefixLift 5451221
  have htrace : WordTrace (prefixWord ++ tailWord_5451221) baseStart_5451221 baseEnd_5451221 := by
    simpa [prefixWord, tailWord_5451221, baseEnd_5451221] using wordTrace_append hprefix tailTrace_5451221
  have hstable : (prefixWord ++ tailWord_5451221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451221).length < 2 ^ (prefixWord ++ tailWord_5451221).sum := by decide
  have hdescent : baseEnd_5451221 < baseStart_5451221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451244 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_5451244 : Nat := 118140960795 + 5451244 * 2 ^ 59
def prefixEnd_5451244 : Nat := 4983230072969 + 3 ^ 40 * 5451244 * 2
def baseEnd_5451244 : Nat := 933036112312658405493397

theorem tailTrace_5451244 : CollatzResearch.WordTrace tailWord_5451244 prefixEnd_5451244 933036112312658405493397 := by
  unfold tailWord_5451244
  simp only [CollatzResearch.WordTrace]
  refine ⟨99411601331540730599872393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132548801775387640799829857 99411601331540730599872393)
  ·
    refine ⟨74558700998655547949904295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99411601331540730599872393 74558700998655547949904295)
    ·
      refine ⟨111838051497983321924856443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74558700998655547949904295 111838051497983321924856443)
      ·
        refine ⟨167757077246974982887284665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111838051497983321924856443 167757077246974982887284665)
        ·
          refine ⟨125817807935231237165463499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167757077246974982887284665 125817807935231237165463499)
          ·
            refine ⟨188726711902846855748195249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125817807935231237165463499 188726711902846855748195249)
            ·
              refine ⟨141545033927135141811146437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188726711902846855748195249 141545033927135141811146437)
              ·
                refine ⟨26539693861337839089589957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141545033927135141811146437 26539693861337839089589957)
                ·
                  refine ⟨4976192599000844829298117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26539693861337839089589957 4976192599000844829298117)
                  ·
                    refine ⟨933036112312658405493397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976192599000844829298117 933036112312658405493397)
                    ·
                      rfl

theorem cell23_5451244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_5451244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451244 prefixEnd_5451244 := by exact prefixLift 5451244
  have htrace : WordTrace (prefixWord ++ tailWord_5451244) baseStart_5451244 baseEnd_5451244 := by
    simpa [prefixWord, tailWord_5451244, baseEnd_5451244] using wordTrace_append hprefix tailTrace_5451244
  have hstable : (prefixWord ++ tailWord_5451244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451244).length < 2 ^ (prefixWord ++ tailWord_5451244).sum := by decide
  have hdescent : baseEnd_5451244 < baseStart_5451244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451251 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 7, 2, 2]
def baseStart_5451251 : Nat := 118140960795 + 5451251 * 2 ^ 59
def prefixEnd_5451251 : Nat := 4983230072969 + 3 ^ 40 * 5451251 * 2
def baseEnd_5451251 : Nat := 2799111931302556689092659

theorem tailTrace_5451251 : CollatzResearch.WordTrace tailWord_5451251 prefixEnd_5451251 2799111931302556689092659 := by
  unfold tailWord_5451251
  simp only [CollatzResearch.WordTrace]
  refine ⟨198823457974056101395249607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132548971982704067596833071 198823457974056101395249607)
  ·
    refine ⟨298235186961084152092874411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198823457974056101395249607 298235186961084152092874411)
    ·
      refine ⟨447352780441626228139311617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298235186961084152092874411 447352780441626228139311617)
      ·
        refine ⟨335514585331219671104483713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447352780441626228139311617 335514585331219671104483713)
        ·
          refine ⟨251635938998414753328362785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335514585331219671104483713 251635938998414753328362785)
          ·
            refine ⟨188726954248811064996272089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251635938998414753328362785 188726954248811064996272089)
            ·
              refine ⟨141545215686608298747204067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188726954248811064996272089 141545215686608298747204067)
              ·
                refine ⟨212317823529912448120806101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141545215686608298747204067 212317823529912448120806101)
                ·
                  refine ⟨4976198988982323002831393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 212317823529912448120806101 4976198988982323002831393)
                  ·
                    refine ⟨3732149241736742252123545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4976198988982323002831393 3732149241736742252123545)
                    ·
                      refine ⟨2799111931302556689092659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732149241736742252123545 2799111931302556689092659)
                      ·
                        rfl

theorem cell23_5451251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 2, 2].length) (baseStart_5451251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451251 prefixEnd_5451251 := by exact prefixLift 5451251
  have htrace : WordTrace (prefixWord ++ tailWord_5451251) baseStart_5451251 baseEnd_5451251 := by
    simpa [prefixWord, tailWord_5451251, baseEnd_5451251] using wordTrace_append hprefix tailTrace_5451251
  have hstable : (prefixWord ++ tailWord_5451251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451251).length < 2 ^ (prefixWord ++ tailWord_5451251).sum := by decide
  have hdescent : baseEnd_5451251 < baseStart_5451251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451261 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_5451261 : Nat := 118140960795 + 5451261 * 2 ^ 59
def prefixEnd_5451261 : Nat := 4983230072969 + 3 ^ 40 * 5451261 * 2
def baseEnd_5451261 : Nat := 933039022036367216655871

theorem tailTrace_5451261 : CollatzResearch.WordTrace tailWord_5451261 prefixEnd_5451261 933039022036367216655871 := by
  unfold tailWord_5451261
  simp only [CollatzResearch.WordTrace]
  refine ⟨198823822704019873103113637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132549215136013248735409091 198823822704019873103113637)
  ·
    refine ⟨37279466757003726206833807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198823822704019873103113637 37279466757003726206833807)
    ·
      refine ⟨55919200135505589310250711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37279466757003726206833807 55919200135505589310250711)
      ·
        refine ⟨83878800203258383965376067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55919200135505589310250711 83878800203258383965376067)
        ·
          refine ⟨125818200304887575948064101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83878800203258383965376067 125818200304887575948064101)
          ·
            refine ⟨23590912557166420490262019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125818200304887575948064101 23590912557166420490262019)
            ·
              refine ⟨35386368835749630735393029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23590912557166420490262019 35386368835749630735393029)
              ·
                refine ⟨6634944156703055762886193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35386368835749630735393029 6634944156703055762886193)
                ·
                  refine ⟨4976208117527291822164645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6634944156703055762886193 4976208117527291822164645)
                  ·
                    refine ⟨933039022036367216655871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976208117527291822164645 933039022036367216655871)
                    ·
                      rfl

theorem cell23_5451261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_5451261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451261 prefixEnd_5451261 := by exact prefixLift 5451261
  have htrace : WordTrace (prefixWord ++ tailWord_5451261) baseStart_5451261 baseEnd_5451261 := by
    simpa [prefixWord, tailWord_5451261, baseEnd_5451261] using wordTrace_append hprefix tailTrace_5451261
  have hstable : (prefixWord ++ tailWord_5451261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451261).length < 2 ^ (prefixWord ++ tailWord_5451261).sum := by decide
  have hdescent : baseEnd_5451261 < baseStart_5451261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451267 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 7]
def baseStart_5451267 : Nat := 118140960795 + 5451267 * 2 ^ 59
def prefixEnd_5451267 : Nat := 4983230072969 + 3 ^ 40 * 5451267 * 2
def baseEnd_5451267 : Nat := 2799120146993028626492585

theorem tailTrace_5451267 : CollatzResearch.WordTrace tailWord_5451267 prefixEnd_5451267 2799120146993028626492585 := by
  unfold tailWord_5451267
  simp only [CollatzResearch.WordTrace]
  refine ⟨198824041541998136127832055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132549361027998757418554703 198824041541998136127832055)
  ·
    refine ⟨298236062312997204191748083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198824041541998136127832055 298236062312997204191748083)
    ·
      refine ⟨447354093469495806287622125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298236062312997204191748083 447354093469495806287622125)
      ·
        refine ⟨167757785051060927357858297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447354093469495806287622125 167757785051060927357858297)
        ·
          refine ⟨125818338788295695518393723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167757785051060927357858297 125818338788295695518393723)
          ·
            refine ⟨188727508182443543277590585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125818338788295695518393723 188727508182443543277590585)
            ·
              refine ⟨141545631136832657458192939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188727508182443543277590585 141545631136832657458192939)
              ·
                refine ⟨212318446705248986187289409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141545631136832657458192939 212318446705248986187289409)
                ·
                  refine ⟨159238835028936739640467057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212318446705248986187289409 159238835028936739640467057)
                  ·
                    refine ⟨119429126271702554730350293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159238835028936739640467057 119429126271702554730350293)
                    ·
                      refine ⟨2799120146993028626492585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119429126271702554730350293 2799120146993028626492585)
                      ·
                        rfl

theorem cell23_5451267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_5451267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451267 prefixEnd_5451267 := by exact prefixLift 5451267
  have htrace : WordTrace (prefixWord ++ tailWord_5451267) baseStart_5451267 baseEnd_5451267 := by
    simpa [prefixWord, tailWord_5451267, baseEnd_5451267] using wordTrace_append hprefix tailTrace_5451267
  have hstable : (prefixWord ++ tailWord_5451267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451267).length < 2 ^ (prefixWord ++ tailWord_5451267).sum := by decide
  have hdescent : baseEnd_5451267 < baseStart_5451267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451271 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_5451271 : Nat := 118140960795 + 5451271 * 2 ^ 59
def prefixEnd_5451271 : Nat := 4983230072969 + 3 ^ 40 * 5451271 * 2
def baseEnd_5451271 : Nat := 2799122200915646610842567

theorem tailTrace_5451271 : CollatzResearch.WordTrace tailWord_5451271 prefixEnd_5451271 2799122200915646610842567 := by
  unfold tailWord_5451271
  simp only [CollatzResearch.WordTrace]
  refine ⟨198824187433983644810977667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132549458289322429873985111 198824187433983644810977667)
  ·
    refine ⟨298236281150975467216466501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198824187433983644810977667 298236281150975467216466501)
    ·
      refine ⟨55919302715807900103087469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298236281150975467216466501 55919302715807900103087469)
      ·
        refine ⟨20969738518427962538657801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55919302715807900103087469 20969738518427962538657801)
        ·
          refine ⟨15727303888820971903993351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20969738518427962538657801 15727303888820971903993351)
          ·
            refine ⟨23590955833231457855990027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15727303888820971903993351 23590955833231457855990027)
            ·
              refine ⟨35386433749847186783985041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23590955833231457855990027 35386433749847186783985041)
              ·
                refine ⟨26539825312385390087988781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35386433749847186783985041 26539825312385390087988781)
                ·
                  refine ⟨9952434492144521282995793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26539825312385390087988781 9952434492144521282995793)
                  ·
                    refine ⟨7464325869108390962246845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9952434492144521282995793 7464325869108390962246845)
                    ·
                      refine ⟨2799122200915646610842567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464325869108390962246845 2799122200915646610842567)
                      ·
                        rfl

theorem cell23_5451271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_5451271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451271 prefixEnd_5451271 := by exact prefixLift 5451271
  have htrace : WordTrace (prefixWord ++ tailWord_5451271) baseStart_5451271 baseEnd_5451271 := by
    simpa [prefixWord, tailWord_5451271, baseEnd_5451271] using wordTrace_append hprefix tailTrace_5451271
  have hstable : (prefixWord ++ tailWord_5451271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451271).length < 2 ^ (prefixWord ++ tailWord_5451271).sum := by decide
  have hdescent : baseEnd_5451271 < baseStart_5451271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451274 : List Nat := [3, 1, 2, 2, 2, 2, 3, 8]
def baseStart_5451274 : Nat := 118140960795 + 5451274 * 2 ^ 59
def prefixEnd_5451274 : Nat := 4983230072969 + 3 ^ 40 * 5451274 * 2
def baseEnd_5451274 : Nat := 103671249679911485152039

theorem tailTrace_5451274 : CollatzResearch.WordTrace tailWord_5451274 prefixEnd_5451274 103671249679911485152039 := by
  unfold tailWord_5451274
  simp only [CollatzResearch.WordTrace]
  refine ⟨49706074213243194080834219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132549531235315184215557917 49706074213243194080834219)
  ·
    refine ⟨74559111319864791121251329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49706074213243194080834219 74559111319864791121251329)
    ·
      refine ⟨55919333489898593340938497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74559111319864791121251329 55919333489898593340938497)
      ·
        refine ⟨41939500117423945005703873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55919333489898593340938497 41939500117423945005703873)
        ·
          refine ⟨31454625088067958754277905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41939500117423945005703873 31454625088067958754277905)
          ·
            refine ⟨23590968816050969065708429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31454625088067958754277905 23590968816050969065708429)
            ·
              refine ⟨8846613306019113399640661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23590968816050969065708429 8846613306019113399640661)
              ·
                refine ⟨103671249679911485152039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8846613306019113399640661 103671249679911485152039)
                ·
                  rfl

theorem cell23_5451274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 8].length) (baseStart_5451274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451274 prefixEnd_5451274 := by exact prefixLift 5451274
  have htrace : WordTrace (prefixWord ++ tailWord_5451274) baseStart_5451274 baseEnd_5451274 := by
    simpa [prefixWord, tailWord_5451274, baseEnd_5451274] using wordTrace_append hprefix tailTrace_5451274
  have hstable : (prefixWord ++ tailWord_5451274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451274).length < 2 ^ (prefixWord ++ tailWord_5451274).sum := by decide
  have hdescent : baseEnd_5451274 < baseStart_5451274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451301 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_5451301 : Nat := 118140960795 + 5451301 * 2 ^ 59
def prefixEnd_5451301 : Nat := 4983230072969 + 3 ^ 40 * 5451301 * 2
def baseEnd_5451301 : Nat := 2799137605335281493467429

theorem tailTrace_5451301 : CollatzResearch.WordTrace tailWord_5451301 prefixEnd_5451301 2799137605335281493467429 := by
  unfold tailWord_5451301
  simp only [CollatzResearch.WordTrace]
  refine ⟨198825281623874959934569757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132550187749249973289713171 198825281623874959934569757)
  ·
    refine ⟨74559480608953109975463659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198825281623874959934569757 74559480608953109975463659)
    ·
      refine ⟨111839220913429664963195489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74559480608953109975463659 111839220913429664963195489)
      ·
        refine ⟨83879415685072248722396617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111839220913429664963195489 83879415685072248722396617)
        ·
          refine ⟨62909561763804186541797463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83879415685072248722396617 62909561763804186541797463)
          ·
            refine ⟨94364342645706279812696195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62909561763804186541797463 94364342645706279812696195)
            ·
              refine ⟨141546513968559419719044293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94364342645706279812696195 141546513968559419719044293)
              ·
                refine ⟨26539971369104891197320805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141546513968559419719044293 26539971369104891197320805)
                ·
                  refine ⟨4976244631707167099497651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26539971369104891197320805 4976244631707167099497651)
                  ·
                    refine ⟨7464366947560750649246477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976244631707167099497651 7464366947560750649246477)
                    ·
                      refine ⟨2799137605335281493467429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464366947560750649246477 2799137605335281493467429)
                      ·
                        rfl

theorem cell23_5451301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_5451301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451301 prefixEnd_5451301 := by exact prefixLift 5451301
  have htrace : WordTrace (prefixWord ++ tailWord_5451301) baseStart_5451301 baseEnd_5451301 := by
    simpa [prefixWord, tailWord_5451301, baseEnd_5451301] using wordTrace_append hprefix tailTrace_5451301
  have hstable : (prefixWord ++ tailWord_5451301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451301).length < 2 ^ (prefixWord ++ tailWord_5451301).sum := by decide
  have hdescent : baseEnd_5451301 < baseStart_5451301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451335 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_5451335 : Nat := 118140960795 + 5451335 * 2 ^ 59
def prefixEnd_5451335 : Nat := 4983230072969 + 3 ^ 40 * 5451335 * 2
def baseEnd_5451335 : Nat := 2799155063677534360442273

theorem tailTrace_5451335 : CollatzResearch.WordTrace tailWord_5451335 prefixEnd_5451335 2799155063677534360442273 := by
  unfold tailWord_5451335
  simp only [CollatzResearch.WordTrace]
  refine ⟨198826521705751783741307459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132551014470501189160871639 198826521705751783741307459)
  ·
    refine ⟨298239782558627675611961189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198826521705751783741307459 298239782558627675611961189)
    ·
      refine ⟨55919959229742689177242723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298239782558627675611961189 55919959229742689177242723)
      ·
        refine ⟨83879938844614033765864085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55919959229742689177242723 83879938844614033765864085)
        ·
          refine ⟨3931872133341282832774879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83879938844614033765864085 3931872133341282832774879)
          ·
            refine ⟨5897808200011924249162319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3931872133341282832774879 5897808200011924249162319)
            ·
              refine ⟨8846712300017886373743479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5897808200011924249162319 8846712300017886373743479)
              ·
                refine ⟨13270068450026829560615219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8846712300017886373743479 13270068450026829560615219)
                ·
                  refine ⟨19905102675040244340922829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13270068450026829560615219 19905102675040244340922829)
                  ·
                    refine ⟨7464413503140091627846061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19905102675040244340922829 7464413503140091627846061)
                    ·
                      refine ⟨2799155063677534360442273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464413503140091627846061 2799155063677534360442273)
                      ·
                        rfl

theorem cell23_5451335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_5451335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451335 prefixEnd_5451335 := by exact prefixLift 5451335
  have htrace : WordTrace (prefixWord ++ tailWord_5451335) baseStart_5451335 baseEnd_5451335 := by
    simpa [prefixWord, tailWord_5451335, baseEnd_5451335] using wordTrace_append hprefix tailTrace_5451335
  have hstable : (prefixWord ++ tailWord_5451335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451335).length < 2 ^ (prefixWord ++ tailWord_5451335).sum := by decide
  have hdescent : baseEnd_5451335 < baseStart_5451335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451344 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_5451344 : Nat := 118140960795 + 5451344 * 2 ^ 59
def prefixEnd_5451344 : Nat := 4983230072969 + 3 ^ 40 * 5451344 * 2
def baseEnd_5451344 : Nat := 2799159685003424825229731

theorem tailTrace_5451344 : CollatzResearch.WordTrace tailWord_5451344 prefixEnd_5451344 2799159685003424825229731 := by
  unfold tailWord_5451344
  simp only [CollatzResearch.WordTrace]
  refine ⟨99413424981359589139192543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132551233308479452185590057 99413424981359589139192543)
  ·
    refine ⟨149120137472039383708788815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99413424981359589139192543 149120137472039383708788815)
    ·
      refine ⟨223680206208059075563183223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149120137472039383708788815 223680206208059075563183223)
      ·
        refine ⟨335520309312088613344774835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223680206208059075563183223 335520309312088613344774835)
        ·
          refine ⟨503280463968132920017162253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335520309312088613344774835 503280463968132920017162253)
          ·
            refine ⟨188730173988049845006435845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 503280463968132920017162253 188730173988049845006435845)
            ·
              refine ⟨35386907622759345938706721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188730173988049845006435845 35386907622759345938706721)
              ·
                refine ⟨26540180717069509454030041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35386907622759345938706721 26540180717069509454030041)
                ·
                  refine ⟨19905135537802132090522531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26540180717069509454030041 19905135537802132090522531)
                  ·
                    refine ⟨29857703306703198135783797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19905135537802132090522531 29857703306703198135783797)
                    ·
                      refine ⟨2799159685003424825229731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29857703306703198135783797 2799159685003424825229731)
                      ·
                        rfl

theorem cell23_5451344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_5451344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451344 prefixEnd_5451344 := by exact prefixLift 5451344
  have htrace : WordTrace (prefixWord ++ tailWord_5451344) baseStart_5451344 baseEnd_5451344 := by
    simpa [prefixWord, tailWord_5451344, baseEnd_5451344] using wordTrace_append hprefix tailTrace_5451344
  have hstable : (prefixWord ++ tailWord_5451344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451344).length < 2 ^ (prefixWord ++ tailWord_5451344).sum := by decide
  have hdescent : baseEnd_5451344 < baseStart_5451344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451354 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_5451354 : Nat := 118140960795 + 5451354 * 2 ^ 59
def prefixEnd_5451354 : Nat := 4983230072969 + 3 ^ 40 * 5451354 * 2
def baseEnd_5451354 : Nat := 2799164819809969786104685

theorem tailTrace_5451354 : CollatzResearch.WordTrace tailWord_5451354 prefixEnd_5451354 2799164819809969786104685 := by
  unfold tailWord_5451354
  simp only [CollatzResearch.WordTrace]
  refine ⟨49706803673170737496562279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132551476461788633324166077 49706803673170737496562279)
  ·
    refine ⟨74560205509756106244843419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49706803673170737496562279 74560205509756106244843419)
    ·
      refine ⟨111840308264634159367265129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74560205509756106244843419 111840308264634159367265129)
      ·
        refine ⟨83880231198475619525448847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111840308264634159367265129 83880231198475619525448847)
        ·
          refine ⟨125820346797713429288173271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83880231198475619525448847 125820346797713429288173271)
          ·
            refine ⟨188730520196570143932259907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125820346797713429288173271 188730520196570143932259907)
            ·
              refine ⟨283095780294855215898389861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188730520196570143932259907 283095780294855215898389861)
              ·
                refine ⟨53080458805285352980948099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283095780294855215898389861 53080458805285352980948099)
                ·
                  refine ⟨79620688207928029471422149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53080458805285352980948099 79620688207928029471422149)
                  ·
                    refine ⟨14928879038986505525891653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79620688207928029471422149 14928879038986505525891653)
                    ·
                      refine ⟨2799164819809969786104685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14928879038986505525891653 2799164819809969786104685)
                      ·
                        rfl

theorem cell23_5451354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_5451354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451354 prefixEnd_5451354 := by exact prefixLift 5451354
  have htrace : WordTrace (prefixWord ++ tailWord_5451354) baseStart_5451354 baseEnd_5451354 := by
    simpa [prefixWord, tailWord_5451354, baseEnd_5451354] using wordTrace_append hprefix tailTrace_5451354
  have hstable : (prefixWord ++ tailWord_5451354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451354).length < 2 ^ (prefixWord ++ tailWord_5451354).sum := by decide
  have hdescent : baseEnd_5451354 < baseStart_5451354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451404 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_5451404 : Nat := 118140960795 + 5451404 * 2 ^ 59
def prefixEnd_5451404 : Nat := 4983230072969 + 3 ^ 40 * 5451404 * 2
def baseEnd_5451404 : Nat := 2799190493842694590479455

theorem tailTrace_5451404 : CollatzResearch.WordTrace tailWord_5451404 prefixEnd_5451404 2799190493842694590479455 := by
  unfold tailWord_5451404
  simp only [CollatzResearch.WordTrace]
  refine ⟨99414519171250904262784633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132552692228334539017046177 99414519171250904262784633)
  ·
    refine ⟨74560889378438178197088475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99414519171250904262784633 74560889378438178197088475)
    ·
      refine ⟨111841334067657267295632713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74560889378438178197088475 111841334067657267295632713)
      ·
        refine ⟨83881000550742950471724535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111841334067657267295632713 83881000550742950471724535)
        ·
          refine ⟨125821500826114425707586803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83881000550742950471724535 125821500826114425707586803)
          ·
            refine ⟨188732251239171638561380205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125821500826114425707586803 188732251239171638561380205)
            ·
              refine ⟨70774594214689364460517577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188732251239171638561380205 70774594214689364460517577)
              ·
                refine ⟨53080945661017023345388183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70774594214689364460517577 53080945661017023345388183)
                ·
                  refine ⟨79621418491525535018082275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53080945661017023345388183 79621418491525535018082275)
                  ·
                    refine ⟨119432127737288302527123413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79621418491525535018082275 119432127737288302527123413)
                    ·
                      refine ⟨2799190493842694590479455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119432127737288302527123413 2799190493842694590479455)
                      ·
                        rfl

theorem cell23_5451404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_5451404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451404 prefixEnd_5451404 := by exact prefixLift 5451404
  have htrace : WordTrace (prefixWord ++ tailWord_5451404) baseStart_5451404 baseEnd_5451404 := by
    simpa [prefixWord, tailWord_5451404, baseEnd_5451404] using wordTrace_append hprefix tailTrace_5451404
  have hstable : (prefixWord ++ tailWord_5451404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451404).length < 2 ^ (prefixWord ++ tailWord_5451404).sum := by decide
  have hdescent : baseEnd_5451404 < baseStart_5451404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451451 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 3]
def baseStart_5451451 : Nat := 118140960795 + 5451451 * 2 ^ 59
def prefixEnd_5451451 : Nat := 4983230072969 + 3 ^ 40 * 5451451 * 2
def baseEnd_5451451 : Nat := 2799214627433455906591739

theorem tailTrace_5451451 : CollatzResearch.WordTrace tailWord_5451451 prefixEnd_5451451 2799214627433455906591739 := by
  unfold tailWord_5451451
  simp only [CollatzResearch.WordTrace]
  refine ⟨198830752573331535552530207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132553835048887690368353471 198830752573331535552530207)
  ·
    refine ⟨298246128859997303328795311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198830752573331535552530207 298246128859997303328795311)
    ·
      refine ⟨447369193289995954993192967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298246128859997303328795311 447369193289995954993192967)
      ·
        refine ⟨671053789934993932489789451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447369193289995954993192967 671053789934993932489789451)
        ·
          refine ⟨1006580684902490898734684177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671053789934993932489789451 1006580684902490898734684177)
          ·
            refine ⟨754935513676868174051013133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006580684902490898734684177 754935513676868174051013133)
            ·
              refine ⟨283100817628825565269129925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 754935513676868174051013133 283100817628825565269129925)
              ·
                refine ⟨53081403305404793487961861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283100817628825565269129925 53081403305404793487961861)
                ·
                  refine ⟨9952763119763398778992849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53081403305404793487961861 9952763119763398778992849)
                  ·
                    refine ⟨7464572339822549084244637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9952763119763398778992849 7464572339822549084244637)
                    ·
                      refine ⟨2799214627433455906591739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464572339822549084244637 2799214627433455906591739)
                      ·
                        rfl

theorem cell23_5451451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 3].length) (baseStart_5451451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451451 prefixEnd_5451451 := by exact prefixLift 5451451
  have htrace : WordTrace (prefixWord ++ tailWord_5451451) baseStart_5451451 baseEnd_5451451 := by
    simpa [prefixWord, tailWord_5451451, baseEnd_5451451] using wordTrace_append hprefix tailTrace_5451451
  have hstable : (prefixWord ++ tailWord_5451451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451451).length < 2 ^ (prefixWord ++ tailWord_5451451).sum := by decide
  have hdescent : baseEnd_5451451 < baseStart_5451451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451462 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_5451462 : Nat := 118140960795 + 5451462 * 2 ^ 59
def prefixEnd_5451462 : Nat := 4983230072969 + 3 ^ 40 * 5451462 * 2
def baseEnd_5451462 : Nat := 933073425240218454518063

theorem tailTrace_5451462 : CollatzResearch.WordTrace tailWord_5451462 prefixEnd_5451462 933073425240218454518063 := by
  unfold tailWord_5451462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213473555509115138474395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132554102517527789620787093 6213473555509115138474395)
  ·
    refine ⟨9320210333263672707711593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213473555509115138474395 9320210333263672707711593)
    ·
      refine ⟨6990157749947754530783695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9320210333263672707711593 6990157749947754530783695)
      ·
        refine ⟨10485236624921631796175543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990157749947754530783695 10485236624921631796175543)
        ·
          refine ⟨15727854937382447694263315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10485236624921631796175543 15727854937382447694263315)
          ·
            refine ⟨23591782406073671541394973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15727854937382447694263315 23591782406073671541394973)
            ·
              refine ⟨8846918402277626828023115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23591782406073671541394973 8846918402277626828023115)
              ·
                refine ⟨13270377603416440242034673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8846918402277626828023115 13270377603416440242034673)
                ·
                  refine ⟨9952783202562330181526005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13270377603416440242034673 9952783202562330181526005)
                  ·
                    refine ⟨933073425240218454518063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9952783202562330181526005 933073425240218454518063)
                    ·
                      rfl

theorem cell23_5451462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_5451462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451462 prefixEnd_5451462 := by exact prefixLift 5451462
  have htrace : WordTrace (prefixWord ++ tailWord_5451462) baseStart_5451462 baseEnd_5451462 := by
    simpa [prefixWord, tailWord_5451462, baseEnd_5451462] using wordTrace_append hprefix tailTrace_5451462
  have hstable : (prefixWord ++ tailWord_5451462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451462).length < 2 ^ (prefixWord ++ tailWord_5451462).sum := by decide
  have hdescent : baseEnd_5451462 < baseStart_5451462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451531 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 1, 6]
def baseStart_5451531 : Nat := 118140960795 + 5451531 * 2 ^ 59
def prefixEnd_5451531 : Nat := 4983230072969 + 3 ^ 40 * 5451531 * 2
def baseEnd_5451531 : Nat := 933085235295271864530457

theorem tailTrace_5451531 : CollatzResearch.WordTrace tailWord_5451531 prefixEnd_5451531 933085235295271864530457 := by
  unfold tailWord_5451531
  simp only [CollatzResearch.WordTrace]
  refine ⟨198833670413041709215442447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132555780275361139476961631 198833670413041709215442447)
  ·
    refine ⟨298250505619562563823163671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198833670413041709215442447 298250505619562563823163671)
    ·
      refine ⟨447375758429343845734745507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298250505619562563823163671 447375758429343845734745507)
      ·
        refine ⟨671063637644015768602118261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447375758429343845734745507 671063637644015768602118261)
        ·
          refine ⟨62912216029126478306448587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 671063637644015768602118261 62912216029126478306448587)
          ·
            refine ⟨94368324043689717459672881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62912216029126478306448587 94368324043689717459672881)
            ·
              refine ⟨70776243032767288094754661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94368324043689717459672881 70776243032767288094754661)
              ·
                refine ⟨13270545568643866517766499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70776243032767288094754661 13270545568643866517766499)
                ·
                  refine ⟨19905818352965799776649749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13270545568643866517766499 19905818352965799776649749)
                  ·
                    refine ⟨933085235295271864530457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19905818352965799776649749 933085235295271864530457)
                    ·
                      rfl

theorem cell23_5451531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 6].length) (baseStart_5451531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451531 prefixEnd_5451531 := by exact prefixLift 5451531
  have htrace : WordTrace (prefixWord ++ tailWord_5451531) baseStart_5451531 baseEnd_5451531 := by
    simpa [prefixWord, tailWord_5451531, baseEnd_5451531] using wordTrace_append hprefix tailTrace_5451531
  have hstable : (prefixWord ++ tailWord_5451531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451531).length < 2 ^ (prefixWord ++ tailWord_5451531).sum := by decide
  have hdescent : baseEnd_5451531 < baseStart_5451531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451532 : List Nat := [2, 2, 1, 2, 2, 1, 5, 3, 1, 1, 3]
def baseStart_5451532 : Nat := 118140960795 + 5451532 * 2 ^ 59
def prefixEnd_5451532 : Nat := 4983230072969 + 3 ^ 40 * 5451532 * 2
def baseEnd_5451532 : Nat := 2799256219366470089678867

theorem tailTrace_5451532 : CollatzResearch.WordTrace tailWord_5451532 prefixEnd_5451532 2799256219366470089678867 := by
  unfold tailWord_5451532
  simp only [CollatzResearch.WordTrace]
  refine ⟨99416853443019043193114425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132555804590692057590819233 99416853443019043193114425)
  ·
    refine ⟨74562640082264282394835819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99416853443019043193114425 74562640082264282394835819)
    ·
      refine ⟨111843960123396423592253729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74562640082264282394835819 111843960123396423592253729)
      ·
        refine ⟨83882970092547317694190297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111843960123396423592253729 83882970092547317694190297)
        ·
          refine ⟨62912227569410488270642723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83882970092547317694190297 62912227569410488270642723)
          ·
            refine ⟨94368341354115732405964085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62912227569410488270642723 94368341354115732405964085)
            ·
              refine ⟨8847032001948349913059133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94368341354115732405964085 8847032001948349913059133)
              ·
                refine ⟨3317637000730631217397175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8847032001948349913059133 3317637000730631217397175)
                ·
                  refine ⟨4976455501095946826095763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317637000730631217397175 4976455501095946826095763)
                  ·
                    refine ⟨7464683251643920239143645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976455501095946826095763 7464683251643920239143645)
                    ·
                      refine ⟨2799256219366470089678867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464683251643920239143645 2799256219366470089678867)
                      ·
                        rfl

theorem cell23_5451532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_5451532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451532 prefixEnd_5451532 := by exact prefixLift 5451532
  have htrace : WordTrace (prefixWord ++ tailWord_5451532) baseStart_5451532 baseEnd_5451532 := by
    simpa [prefixWord, tailWord_5451532, baseEnd_5451532] using wordTrace_append hprefix tailTrace_5451532
  have hstable : (prefixWord ++ tailWord_5451532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451532).length < 2 ^ (prefixWord ++ tailWord_5451532).sum := by decide
  have hdescent : baseEnd_5451532 < baseStart_5451532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451548 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_5451548 : Nat := 118140960795 + 5451548 * 2 ^ 59
def prefixEnd_5451548 : Nat := 4983230072969 + 3 ^ 40 * 5451548 * 2
def baseEnd_5451548 : Nat := 933088145018980675692931

theorem tailTrace_5451548 : CollatzResearch.WordTrace tailWord_5451548 prefixEnd_5451548 933088145018980675692931 := by
  unfold tailWord_5451548
  simp only [CollatzResearch.WordTrace]
  refine ⟨99417145226990060559405649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132556193635986747412540865 99417145226990060559405649)
  ·
    refine ⟨74562858920242545419554237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99417145226990060559405649 74562858920242545419554237)
    ·
      refine ⟨27961072095090954532332839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74562858920242545419554237 27961072095090954532332839)
      ·
        refine ⟨41941608142636431798499259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27961072095090954532332839 41941608142636431798499259)
        ·
          refine ⟨62912412213954647697748889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41941608142636431798499259 62912412213954647697748889)
          ·
            refine ⟨47184309160465985773311667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62912412213954647697748889 47184309160465985773311667)
            ·
              refine ⟨70776463740698978659967501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47184309160465985773311667 70776463740698978659967501)
              ·
                refine ⟨26541173902762116997487813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70776463740698978659967501 26541173902762116997487813)
                ·
                  refine ⟨4976470106767896937028965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26541173902762116997487813 4976470106767896937028965)
                  ·
                    refine ⟨933088145018980675692931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976470106767896937028965 933088145018980675692931)
                    ·
                      rfl

theorem cell23_5451548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_5451548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451548 prefixEnd_5451548 := by exact prefixLift 5451548
  have htrace : WordTrace (prefixWord ++ tailWord_5451548) baseStart_5451548 baseEnd_5451548 := by
    simpa [prefixWord, tailWord_5451548, baseEnd_5451548] using wordTrace_append hprefix tailTrace_5451548
  have hstable : (prefixWord ++ tailWord_5451548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451548).length < 2 ^ (prefixWord ++ tailWord_5451548).sum := by decide
  have hdescent : baseEnd_5451548 < baseStart_5451548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451551 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_5451551 : Nat := 118140960795 + 5451551 * 2 ^ 59
def prefixEnd_5451551 : Nat := 4983230072969 + 3 ^ 40 * 5451551 * 2
def baseEnd_5451551 : Nat := 2799265975498905515341279

theorem tailTrace_5451551 : CollatzResearch.WordTrace tailWord_5451551 prefixEnd_5451551 2799265975498905515341279 := by
  unfold tailWord_5451551
  simp only [CollatzResearch.WordTrace]
  refine ⟨198834399872969252631170507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132556266581979501754113671 198834399872969252631170507)
  ·
    refine ⟨298251599809453878946755761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198834399872969252631170507 298251599809453878946755761)
    ·
      refine ⟨223688699857090409210066821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298251599809453878946755761 223688699857090409210066821)
      ·
        refine ⟨41941631223204451726887529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223688699857090409210066821 41941631223204451726887529)
        ·
          refine ⟨31456223417403338795165647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41941631223204451726887529 31456223417403338795165647)
          ·
            refine ⟨47184335126105008192748471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31456223417403338795165647 47184335126105008192748471)
            ·
              refine ⟨70776502689157512289122707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47184335126105008192748471 70776502689157512289122707)
              ·
                refine ⟨106164754033736268433684061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70776502689157512289122707 106164754033736268433684061)
                ·
                  refine ⟨39811782762651100662631523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106164754033736268433684061 39811782762651100662631523)
                  ·
                    refine ⟨59717674143976650993947285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39811782762651100662631523 59717674143976650993947285)
                    ·
                      refine ⟨2799265975498905515341279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59717674143976650993947285 2799265975498905515341279)
                      ·
                        rfl

theorem cell23_5451551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_5451551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451551 prefixEnd_5451551 := by exact prefixLift 5451551
  have htrace : WordTrace (prefixWord ++ tailWord_5451551) baseStart_5451551 baseEnd_5451551 := by
    simpa [prefixWord, tailWord_5451551, baseEnd_5451551] using wordTrace_append hprefix tailTrace_5451551
  have hstable : (prefixWord ++ tailWord_5451551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451551).length < 2 ^ (prefixWord ++ tailWord_5451551).sum := by decide
  have hdescent : baseEnd_5451551 < baseStart_5451551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451572 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_5451572 : Nat := 118140960795 + 5451572 * 2 ^ 59
def prefixEnd_5451572 : Nat := 4983230072969 + 3 ^ 40 * 5451572 * 2
def baseEnd_5451572 : Nat := 2799276758592649933178683

theorem tailTrace_5451572 : CollatzResearch.WordTrace tailWord_5451572 prefixEnd_5451572 2799276758592649933178683 := by
  unfold tailWord_5451572
  simp only [CollatzResearch.WordTrace]
  refine ⟨99417582902946586608842485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132556777203928782145123313 99417582902946586608842485)
  ·
    refine ⟨9320398397151242494578983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99417582902946586608842485 9320398397151242494578983)
    ·
      refine ⟨13980597595726863741868475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9320398397151242494578983 13980597595726863741868475)
      ·
        refine ⟨20970896393590295612802713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13980597595726863741868475 20970896393590295612802713)
        ·
          refine ⟨15728172295192721709602035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20970896393590295612802713 15728172295192721709602035)
          ·
            refine ⟨23592258442789082564403053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15728172295192721709602035 23592258442789082564403053)
            ·
              refine ⟨8847096916045905961651145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23592258442789082564403053 8847096916045905961651145)
              ·
                refine ⟨6635322687034429471238359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8847096916045905961651145 6635322687034429471238359)
                ·
                  refine ⟨9952984030551644206857539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6635322687034429471238359 9952984030551644206857539)
                  ·
                    refine ⟨14929476045827466310286309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9952984030551644206857539 14929476045827466310286309)
                    ·
                      refine ⟨2799276758592649933178683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14929476045827466310286309 2799276758592649933178683)
                      ·
                        rfl

theorem cell23_5451572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_5451572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451572 prefixEnd_5451572 := by exact prefixLift 5451572
  have htrace : WordTrace (prefixWord ++ tailWord_5451572) baseStart_5451572 baseEnd_5451572 := by
    simpa [prefixWord, tailWord_5451572, baseEnd_5451572] using wordTrace_append hprefix tailTrace_5451572
  have hstable : (prefixWord ++ tailWord_5451572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451572).length < 2 ^ (prefixWord ++ tailWord_5451572).sum := by decide
  have hdescent : baseEnd_5451572 < baseStart_5451572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451592 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_5451592 : Nat := 118140960795 + 5451592 * 2 ^ 59
def prefixEnd_5451592 : Nat := 4983230072969 + 3 ^ 40 * 5451592 * 2
def baseEnd_5451592 : Nat := 2799287028205739854928591

theorem tailTrace_5451592 : CollatzResearch.WordTrace tailWord_5451592 prefixEnd_5451592 2799287028205739854928591 := by
  unfold tailWord_5451592
  simp only [CollatzResearch.WordTrace]
  refine ⟨99417947632910358316706515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132557263510547144422275353 99417947632910358316706515)
  ·
    refine ⟨149126921449365537475059773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99417947632910358316706515 149126921449365537475059773)
    ·
      refine ⟨55922595543512076553147415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149126921449365537475059773 55922595543512076553147415)
      ·
        refine ⟨83883893315268114829721123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55922595543512076553147415 83883893315268114829721123)
        ·
          refine ⟨125825839972902172244581685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83883893315268114829721123 125825839972902172244581685)
          ·
            refine ⟨11796172497459578647929533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125825839972902172244581685 11796172497459578647929533)
            ·
              refine ⟨4423564686547341992973575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11796172497459578647929533 4423564686547341992973575)
              ·
                refine ⟨6635347029821012989460363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423564686547341992973575 6635347029821012989460363)
                ·
                  refine ⟨9953020544731519484190545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6635347029821012989460363 9953020544731519484190545)
                  ·
                    refine ⟨7464765408548639613142909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9953020544731519484190545 7464765408548639613142909)
                    ·
                      refine ⟨2799287028205739854928591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464765408548639613142909 2799287028205739854928591)
                      ·
                        rfl

theorem cell23_5451592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_5451592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451592 prefixEnd_5451592 := by exact prefixLift 5451592
  have htrace : WordTrace (prefixWord ++ tailWord_5451592) baseStart_5451592 baseEnd_5451592 := by
    simpa [prefixWord, tailWord_5451592, baseEnd_5451592] using wordTrace_append hprefix tailTrace_5451592
  have hstable : (prefixWord ++ tailWord_5451592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451592).length < 2 ^ (prefixWord ++ tailWord_5451592).sum := by decide
  have hdescent : baseEnd_5451592 < baseStart_5451592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451612 : List Nat := [2, 2, 4, 2, 3, 1, 1, 8]
def baseStart_5451612 : Nat := 118140960795 + 5451612 * 2 ^ 59
def prefixEnd_5451612 : Nat := 4983230072969 + 3 ^ 40 * 5451612 * 2
def baseEnd_5451612 : Nat := 103677677696993695432537

theorem tailTrace_5451612 : CollatzResearch.WordTrace tailWord_5451612 prefixEnd_5451612 103677677696993695432537 := by
  unfold tailWord_5451612
  simp only [CollatzResearch.WordTrace]
  refine ⟨99418312362874130024570545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132557749817165506699427393 99418312362874130024570545)
  ·
    refine ⟨74563734272155597518427909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99418312362874130024570545 74563734272155597518427909)
    ·
      refine ⟨13980700176029174534705233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74563734272155597518427909 13980700176029174534705233)
      ·
        refine ⟨10485525132021880901028925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13980700176029174534705233 10485525132021880901028925)
        ·
          refine ⟨3932071924508205337885847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10485525132021880901028925 3932071924508205337885847)
          ·
            refine ⟨5898107886762308006828771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932071924508205337885847 5898107886762308006828771)
            ·
              refine ⟨8847161830143462010243157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898107886762308006828771 8847161830143462010243157)
              ·
                refine ⟨103677677696993695432537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8847161830143462010243157 103677677696993695432537)
                ·
                  rfl

theorem cell23_5451612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 8].length) (baseStart_5451612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451612 prefixEnd_5451612 := by exact prefixLift 5451612
  have htrace : WordTrace (prefixWord ++ tailWord_5451612) baseStart_5451612 baseEnd_5451612 := by
    simpa [prefixWord, tailWord_5451612, baseEnd_5451612] using wordTrace_append hprefix tailTrace_5451612
  have hstable : (prefixWord ++ tailWord_5451612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451612).length < 2 ^ (prefixWord ++ tailWord_5451612).sum := by decide
  have hdescent : baseEnd_5451612 < baseStart_5451612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451615 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 3, 3, 2]
def baseStart_5451615 : Nat := 118140960795 + 5451615 * 2 ^ 59
def prefixEnd_5451615 : Nat := 4983230072969 + 3 ^ 40 * 5451615 * 2
def baseEnd_5451615 : Nat := 2799298838260793264940985

theorem tailTrace_5451615 : CollatzResearch.WordTrace tailWord_5451615 prefixEnd_5451615 2799298838260793264940985 := by
  unfold tailWord_5451615
  simp only [CollatzResearch.WordTrace]
  refine ⟨198836734144737391561500299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132557822763158261041000199 198836734144737391561500299)
  ·
    refine ⟨298255101217106087342250449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198836734144737391561500299 298255101217106087342250449)
    ·
      refine ⟨223691325912829565506687837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298255101217106087342250449 223691325912829565506687837)
      ·
        refine ⟨83884247217311087065007939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223691325912829565506687837 83884247217311087065007939)
        ·
          refine ⟨125826370825966630597511909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83884247217311087065007939 125826370825966630597511909)
          ·
            refine ⟨23592444529868743237033483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125826370825966630597511909 23592444529868743237033483)
            ·
              refine ⟨35388666794803114855550225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23592444529868743237033483 35388666794803114855550225)
              ·
                refine ⟨26541500096102336141662669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35388666794803114855550225 26541500096102336141662669)
                ·
                  refine ⟨9953062536038376053123501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26541500096102336141662669 9953062536038376053123501)
                  ·
                    refine ⟨3732398451014391019921313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9953062536038376053123501 3732398451014391019921313)
                    ·
                      refine ⟨2799298838260793264940985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732398451014391019921313 2799298838260793264940985)
                      ·
                        rfl

theorem cell23_5451615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_5451615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451615 prefixEnd_5451615 := by exact prefixLift 5451615
  have htrace : WordTrace (prefixWord ++ tailWord_5451615) baseStart_5451615 baseEnd_5451615 := by
    simpa [prefixWord, tailWord_5451615, baseEnd_5451615] using wordTrace_append hprefix tailTrace_5451615
  have hstable : (prefixWord ++ tailWord_5451615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451615).length < 2 ^ (prefixWord ++ tailWord_5451615).sum := by decide
  have hdescent : baseEnd_5451615 < baseStart_5451615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451656 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_5451656 : Nat := 118140960795 + 5451656 * 2 ^ 59
def prefixEnd_5451656 : Nat := 4983230072969 + 3 ^ 40 * 5451656 * 2
def baseEnd_5451656 : Nat := 2799319890967627604528297

theorem tailTrace_5451656 : CollatzResearch.WordTrace tailWord_5451656 prefixEnd_5451656 2799319890967627604528297 := by
  unfold tailWord_5451656
  simp only [CollatzResearch.WordTrace]
  refine ⟨99419114768794427781871411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132558819691725903709161881 99419114768794427781871411)
  ·
    refine ⟨149128672153191641672807117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99419114768794427781871411 149128672153191641672807117)
    ·
      refine ⟨55923252057446865627302669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149128672153191641672807117 55923252057446865627302669)
      ·
        refine ⟨20971219521542574610238501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55923252057446865627302669 20971219521542574610238501)
        ·
          refine ⟨3932103660289232739419719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20971219521542574610238501 3932103660289232739419719)
          ·
            refine ⟨5898155490433849109129579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932103660289232739419719 5898155490433849109129579)
            ·
              refine ⟨8847233235650773663694369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898155490433849109129579 8847233235650773663694369)
              ·
                refine ⟨6635424926738080247770777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8847233235650773663694369 6635424926738080247770777)
                ·
                  refine ⟨4976568695053560185828083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6635424926738080247770777 4976568695053560185828083)
                  ·
                    refine ⟨7464853042580340278742125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976568695053560185828083 7464853042580340278742125)
                    ·
                      refine ⟨2799319890967627604528297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464853042580340278742125 2799319890967627604528297)
                      ·
                        rfl

theorem cell23_5451656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_5451656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451656 prefixEnd_5451656 := by exact prefixLift 5451656
  have htrace : WordTrace (prefixWord ++ tailWord_5451656) baseStart_5451656 baseEnd_5451656 := by
    simpa [prefixWord, tailWord_5451656, baseEnd_5451656] using wordTrace_append hprefix tailTrace_5451656
  have hstable : (prefixWord ++ tailWord_5451656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451656).length < 2 ^ (prefixWord ++ tailWord_5451656).sum := by decide
  have hdescent : baseEnd_5451656 < baseStart_5451656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451679 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 1, 4, 2]
def baseStart_5451679 : Nat := 118140960795 + 5451679 * 2 ^ 59
def prefixEnd_5451679 : Nat := 4983230072969 + 3 ^ 40 * 5451679 * 2
def baseEnd_5451679 : Nat := 2799331701022681014540691

theorem tailTrace_5451679 : CollatzResearch.WordTrace tailWord_5451679 prefixEnd_5451679 2799331701022681014540691 := by
  unfold tailWord_5451679
  simp only [CollatzResearch.WordTrace]
  refine ⟨198839068416505530491830091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132559378944337020327886727 198839068416505530491830091)
  ·
    refine ⟨298258602624758295737745137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198839068416505530491830091 298258602624758295737745137)
    ·
      refine ⟨223693951968568721803308853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298258602624758295737745137 223693951968568721803308853)
      ·
        refine ⟨20971307997053317669060205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223693951968568721803308853 20971307997053317669060205)
        ·
          refine ⟨7864240498894994125897577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20971307997053317669060205 7864240498894994125897577)
          ·
            refine ⟨5898180374171245594423183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7864240498894994125897577 5898180374171245594423183)
            ·
              refine ⟨8847270561256868391634775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898180374171245594423183 8847270561256868391634775)
              ·
                refine ⟨13270905841885302587452163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8847270561256868391634775 13270905841885302587452163)
                ·
                  refine ⟨19906358762827953881178245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13270905841885302587452163 19906358762827953881178245)
                  ·
                    refine ⟨3732442268030241352720921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19906358762827953881178245 3732442268030241352720921)
                    ·
                      refine ⟨2799331701022681014540691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732442268030241352720921 2799331701022681014540691)
                      ·
                        rfl

theorem cell23_5451679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_5451679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451679 prefixEnd_5451679 := by exact prefixLift 5451679
  have htrace : WordTrace (prefixWord ++ tailWord_5451679) baseStart_5451679 baseEnd_5451679 := by
    simpa [prefixWord, tailWord_5451679, baseEnd_5451679] using wordTrace_append hprefix tailTrace_5451679
  have hstable : (prefixWord ++ tailWord_5451679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451679).length < 2 ^ (prefixWord ++ tailWord_5451679).sum := by decide
  have hdescent : baseEnd_5451679 < baseStart_5451679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451698 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_5451698 : Nat := 118140960795 + 5451698 * 2 ^ 59
def prefixEnd_5451698 : Nat := 4983230072969 + 3 ^ 40 * 5451698 * 2
def baseEnd_5451698 : Nat := 933113819051705480067701

theorem tailTrace_5451698 : CollatzResearch.WordTrace tailWord_5451698 prefixEnd_5451698 933113819051705480067701 := by
  unfold tailWord_5451698
  simp only [CollatzResearch.WordTrace]
  refine ⟨49709940350859174184192937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132559840935624464491181165 49709940350859174184192937)
  ·
    refine ⟨37282455263144380638144703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49709940350859174184192937 37282455263144380638144703)
    ·
      refine ⟨55923682894716570957217055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37282455263144380638144703 55923682894716570957217055)
      ·
        refine ⟨83885524342074856435825583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55923682894716570957217055 83885524342074856435825583)
        ·
          refine ⟨125828286513112284653738375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83885524342074856435825583 125828286513112284653738375)
          ·
            refine ⟨188742429769668426980607563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125828286513112284653738375 188742429769668426980607563)
            ·
              refine ⟨283113644654502640470911345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188742429769668426980607563 283113644654502640470911345)
              ·
                refine ⟨212335233490876980353183509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283113644654502640470911345 212335233490876980353183509)
                ·
                  refine ⟨9953214069884858454055477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 212335233490876980353183509 9953214069884858454055477)
                  ·
                    refine ⟨933113819051705480067701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9953214069884858454055477 933113819051705480067701)
                    ·
                      rfl

theorem cell23_5451698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_5451698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451698 prefixEnd_5451698 := by exact prefixLift 5451698
  have htrace : WordTrace (prefixWord ++ tailWord_5451698) baseStart_5451698 baseEnd_5451698 := by
    simpa [prefixWord, tailWord_5451698, baseEnd_5451698] using wordTrace_append hprefix tailTrace_5451698
  have hstable : (prefixWord ++ tailWord_5451698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451698).length < 2 ^ (prefixWord ++ tailWord_5451698).sum := by decide
  have hdescent : baseEnd_5451698 < baseStart_5451698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451730 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5451730 : Nat := 118140960795 + 5451730 * 2 ^ 59
def prefixEnd_5451730 : Nat := 4983230072969 + 3 ^ 40 * 5451730 * 2
def baseEnd_5451730 : Nat := 2799357888536060315002957

theorem tailTrace_5451730 : CollatzResearch.WordTrace tailWord_5451730 prefixEnd_5451730 2799357888536060315002957 := by
  unfold tailWord_5451730
  simp only [CollatzResearch.WordTrace]
  refine ⟨49710232134830191550484161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132560619026213844134624429 49710232134830191550484161)
  ·
    refine ⟨37282674101122643662863121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49710232134830191550484161 37282674101122643662863121)
    ·
      refine ⟨27962005575841982747147341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37282674101122643662863121 27962005575841982747147341)
      ·
        refine ⟨10485752090940743530180253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27962005575841982747147341 10485752090940743530180253)
        ·
          refine ⟨3932157034102778823817595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10485752090940743530180253 3932157034102778823817595)
          ·
            refine ⟨5898235551154168235726393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932157034102778823817595 5898235551154168235726393)
            ·
              refine ⟨4423676663365626176794795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5898235551154168235726393 4423676663365626176794795)
              ·
                refine ⟨6635514995048439265192193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423676663365626176794795 6635514995048439265192193)
                ·
                  refine ⟨4976636246286329448894145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6635514995048439265192193 4976636246286329448894145)
                  ·
                    refine ⟨3732477184714747086670609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4976636246286329448894145 3732477184714747086670609)
                    ·
                      refine ⟨2799357888536060315002957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732477184714747086670609 2799357888536060315002957)
                      ·
                        rfl

theorem cell23_5451730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5451730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451730 prefixEnd_5451730 := by exact prefixLift 5451730
  have htrace : WordTrace (prefixWord ++ tailWord_5451730) baseStart_5451730 baseEnd_5451730 := by
    simpa [prefixWord, tailWord_5451730, baseEnd_5451730] using wordTrace_append hprefix tailTrace_5451730
  have hstable : (prefixWord ++ tailWord_5451730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451730).length < 2 ^ (prefixWord ++ tailWord_5451730).sum := by decide
  have hdescent : baseEnd_5451730 < baseStart_5451730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451735 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 1, 6, 2]
def baseStart_5451735 : Nat := 118140960795 + 5451735 * 2 ^ 59
def prefixEnd_5451735 : Nat := 4983230072969 + 3 ^ 40 * 5451735 * 2
def baseEnd_5451735 : Nat := 2799360455939332795440433

theorem tailTrace_5451735 : CollatzResearch.WordTrace tailWord_5451735 prefixEnd_5451735 2799360455939332795440433 := by
  unfold tailWord_5451735
  simp only [CollatzResearch.WordTrace]
  refine ⟨198841110904302652055868659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132560740602868434703912439 198841110904302652055868659)
  ·
    refine ⟨298261666356453978083802989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198841110904302652055868659 298261666356453978083802989)
    ·
      refine ⟨111848124883670241781426121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298261666356453978083802989 111848124883670241781426121)
      ·
        refine ⟨83886093662752681336069591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111848124883670241781426121 83886093662752681336069591)
        ·
          refine ⟨125829140494129022004104387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83886093662752681336069591 125829140494129022004104387)
          ·
            refine ⟨188743710741193533006156581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125829140494129022004104387 188743710741193533006156581)
            ·
              refine ⟨35389445763973787438654359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188743710741193533006156581 35389445763973787438654359)
              ·
                refine ⟨53084168645960681157981539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35389445763973787438654359 53084168645960681157981539)
                ·
                  refine ⟨79626252968941021736972309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53084168645960681157981539 79626252968941021736972309)
                  ·
                    refine ⟨3732480607919110393920577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79626252968941021736972309 3732480607919110393920577)
                    ·
                      refine ⟨2799360455939332795440433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732480607919110393920577 2799360455939332795440433)
                      ·
                        rfl

theorem cell23_5451735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_5451735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451735 prefixEnd_5451735 := by exact prefixLift 5451735
  have htrace : WordTrace (prefixWord ++ tailWord_5451735) baseStart_5451735 baseEnd_5451735 := by
    simpa [prefixWord, tailWord_5451735, baseEnd_5451735] using wordTrace_append hprefix tailTrace_5451735
  have hstable : (prefixWord ++ tailWord_5451735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451735).length < 2 ^ (prefixWord ++ tailWord_5451735).sum := by decide
  have hdescent : baseEnd_5451735 < baseStart_5451735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451745 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 3, 4]
def baseStart_5451745 : Nat := 118140960795 + 5451745 * 2 ^ 59
def prefixEnd_5451745 : Nat := 4983230072969 + 3 ^ 40 * 5451745 * 2
def baseEnd_5451745 : Nat := 933121863581959252105129

theorem tailTrace_5451745 : CollatzResearch.WordTrace tailWord_5451745 prefixEnd_5451745 933121863581959252105129 := by
  unfold tailWord_5451745
  simp only [CollatzResearch.WordTrace]
  refine ⟨198841475634266423763732689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132560983756177615842488459 198841475634266423763732689)
  ·
    refine ⟨149131106725699817822799517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198841475634266423763732689 149131106725699817822799517)
    ·
      refine ⟨55924165022137431683549819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149131106725699817822799517 55924165022137431683549819)
      ·
        refine ⟨83886247533206147525324729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55924165022137431683549819 83886247533206147525324729)
        ·
          refine ⟨62914685649904610643993547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83886247533206147525324729 62914685649904610643993547)
          ·
            refine ⟨94372028474856915965990321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62914685649904610643993547 94372028474856915965990321)
            ·
              refine ⟨70779021356142686974492741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94372028474856915965990321 70779021356142686974492741)
              ·
                refine ⟨13271066504276753807717389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70779021356142686974492741 13271066504276753807717389)
                ·
                  refine ⟨4976649939103782677894021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13271066504276753807717389 4976649939103782677894021)
                  ·
                    refine ⟨933121863581959252105129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976649939103782677894021 933121863581959252105129)
                    ·
                      rfl

theorem cell23_5451745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_5451745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451745 prefixEnd_5451745 := by exact prefixLift 5451745
  have htrace : WordTrace (prefixWord ++ tailWord_5451745) baseStart_5451745 baseEnd_5451745 := by
    simpa [prefixWord, tailWord_5451745, baseEnd_5451745] using wordTrace_append hprefix tailTrace_5451745
  have hstable : (prefixWord ++ tailWord_5451745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451745).length < 2 ^ (prefixWord ++ tailWord_5451745).sum := by decide
  have hdescent : baseEnd_5451745 < baseStart_5451745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451796 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5451796 : Nat := 118140960795 + 5451796 * 2 ^ 59
def prefixEnd_5451796 : Nat := 4983230072969 + 3 ^ 40 * 5451796 * 2
def baseEnd_5451796 : Nat := 933130592753085685592551

theorem tailTrace_5451796 : CollatzResearch.WordTrace tailWord_5451796 prefixEnd_5451796 933130592753085685592551 := by
  unfold tailWord_5451796
  simp only [CollatzResearch.WordTrace]
  refine ⟨99421667878540829736919621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132562223838054439649226161 99421667878540829736919621)
  ·
    refine ⟨18641562727226405575672429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99421667878540829736919621 18641562727226405575672429)
    ·
      refine ⟨6990586022709902090877161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18641562727226405575672429 6990586022709902090877161)
      ·
        refine ⟨5242939517032426568157871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6990586022709902090877161 5242939517032426568157871)
        ·
          refine ⟨7864409275548639852236807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5242939517032426568157871 7864409275548639852236807)
          ·
            refine ⟨11796613913322959778355211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7864409275548639852236807 11796613913322959778355211)
            ·
              refine ⟨17694920869984439667532817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11796613913322959778355211 17694920869984439667532817)
              ·
                refine ⟨13271190652488329750649613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17694920869984439667532817 13271190652488329750649613)
                ·
                  refine ⟨4976696494683123656493605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13271190652488329750649613 4976696494683123656493605)
                  ·
                    refine ⟨933130592753085685592551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976696494683123656493605 933130592753085685592551)
                    ·
                      rfl

theorem cell23_5451796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5451796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451796 prefixEnd_5451796 := by exact prefixLift 5451796
  have htrace : WordTrace (prefixWord ++ tailWord_5451796) baseStart_5451796 baseEnd_5451796 := by
    simpa [prefixWord, tailWord_5451796, baseEnd_5451796] using wordTrace_append hprefix tailTrace_5451796
  have hstable : (prefixWord ++ tailWord_5451796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451796).length < 2 ^ (prefixWord ++ tailWord_5451796).sum := by decide
  have hdescent : baseEnd_5451796 < baseStart_5451796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451802 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_5451802 : Nat := 118140960795 + 5451802 * 2 ^ 59
def prefixEnd_5451802 : Nat := 4983230072969 + 3 ^ 40 * 5451802 * 2
def baseEnd_5451802 : Nat := 2799394859143184033302625

theorem tailTrace_5451802 : CollatzResearch.WordTrace tailWord_5451802 prefixEnd_5451802 2799394859143184033302625 := by
  unfold tailWord_5451802
  simp only [CollatzResearch.WordTrace]
  refine ⟨49710888648764980624639415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132562369730039948332371773 49710888648764980624639415)
  ·
    refine ⟨74566332973147470936959123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49710888648764980624639415 74566332973147470936959123)
    ·
      refine ⟨111849499459721206405438685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74566332973147470936959123 111849499459721206405438685)
      ·
        refine ⟨41943562297395452402039507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111849499459721206405438685 41943562297395452402039507)
        ·
          refine ⟨62915343446093178603059261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41943562297395452402039507 62915343446093178603059261)
          ·
            refine ⟨23593253792284941976147223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62915343446093178603059261 23593253792284941976147223)
            ·
              refine ⟨35389880688427412964220835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23593253792284941976147223 35389880688427412964220835)
              ·
                refine ⟨53084821032641119446331253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35389880688427412964220835 53084821032641119446331253)
                ·
                  refine ⟨4976701971810104948093555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53084821032641119446331253 4976701971810104948093555)
                  ·
                    refine ⟨7465052957715157422140333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976701971810104948093555 7465052957715157422140333)
                    ·
                      refine ⟨2799394859143184033302625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7465052957715157422140333 2799394859143184033302625)
                      ·
                        rfl

theorem cell23_5451802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_5451802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451802 prefixEnd_5451802 := by exact prefixLift 5451802
  have htrace : WordTrace (prefixWord ++ tailWord_5451802) baseStart_5451802 baseEnd_5451802 := by
    simpa [prefixWord, tailWord_5451802, baseEnd_5451802] using wordTrace_append hprefix tailTrace_5451802
  have hstable : (prefixWord ++ tailWord_5451802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451802).length < 2 ^ (prefixWord ++ tailWord_5451802).sum := by decide
  have hdescent : baseEnd_5451802 < baseStart_5451802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451835 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 4, 4]
def baseStart_5451835 : Nat := 118140960795 + 5451835 * 2 ^ 59
def prefixEnd_5451835 : Nat := 4983230072969 + 3 ^ 40 * 5451835 * 2
def baseEnd_5451835 : Nat := 933137268001594134729991

theorem tailTrace_5451835 : CollatzResearch.WordTrace tailWord_5451835 prefixEnd_5451835 933137268001594134729991 := by
  unfold tailWord_5451835
  simp only [CollatzResearch.WordTrace]
  refine ⟨198844758203940369134508959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132563172135960246089672639 198844758203940369134508959)
  ·
    refine ⟨298267137305910553701763439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198844758203940369134508959 298267137305910553701763439)
    ·
      refine ⟨447400705958865830552645159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298267137305910553701763439 447400705958865830552645159)
      ·
        refine ⟨671101058938298745828967739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447400705958865830552645159 671101058938298745828967739)
        ·
          refine ⟨1006651588407448118743451609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671101058938298745828967739 1006651588407448118743451609)
          ·
            refine ⟨754988691305586089057588707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006651588407448118743451609 754988691305586089057588707)
            ·
              refine ⟨1132483036958379133586383061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754988691305586089057588707 1132483036958379133586383061)
              ·
                refine ⟨26542571178712010943430853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1132483036958379133586383061 26542571178712010943430853)
                ·
                  refine ⟨4976732096008502051893285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26542571178712010943430853 4976732096008502051893285)
                  ·
                    refine ⟨933137268001594134729991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976732096008502051893285 933137268001594134729991)
                    ·
                      rfl

theorem cell23_5451835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 4].length) (baseStart_5451835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451835 prefixEnd_5451835 := by exact prefixLift 5451835
  have htrace : WordTrace (prefixWord ++ tailWord_5451835) baseStart_5451835 baseEnd_5451835 := by
    simpa [prefixWord, tailWord_5451835, baseEnd_5451835] using wordTrace_append hprefix tailTrace_5451835
  have hstable : (prefixWord ++ tailWord_5451835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451835).length < 2 ^ (prefixWord ++ tailWord_5451835).sum := by decide
  have hdescent : baseEnd_5451835 < baseStart_5451835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451852 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_5451852 : Nat := 118140960795 + 5451852 * 2 ^ 59
def prefixEnd_5451852 : Nat := 4983230072969 + 3 ^ 40 * 5451852 * 2
def baseEnd_5451852 : Nat := 933140177725302945892465

theorem tailTrace_5451852 : CollatzResearch.WordTrace tailWord_5451852 prefixEnd_5451852 933140177725302945892465 := by
  unfold tailWord_5451852
  simp only [CollatzResearch.WordTrace]
  refine ⟨99422689122439390518938905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132563585496585854025251873 99422689122439390518938905)
  ·
    refine ⟨74567016841829542889204179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99422689122439390518938905 74567016841829542889204179)
    ·
      refine ⟨111850525262744314333806269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74567016841829542889204179 111850525262744314333806269)
      ·
        refine ⟨41943946973529117875177351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111850525262744314333806269 41943946973529117875177351)
        ·
          refine ⟨62915920460293676812766027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41943946973529117875177351 62915920460293676812766027)
          ·
            refine ⟨94373880690440515219149041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62915920460293676812766027 94373880690440515219149041)
            ·
              refine ⟨70780410517830386414361781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94373880690440515219149041 70780410517830386414361781)
              ·
                refine ⟨6635663486046598726346417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70780410517830386414361781 6635663486046598726346417)
                ·
                  refine ⟨4976747614534949044759813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6635663486046598726346417 4976747614534949044759813)
                  ·
                    refine ⟨933140177725302945892465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976747614534949044759813 933140177725302945892465)
                    ·
                      rfl

theorem cell23_5451852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_5451852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451852 prefixEnd_5451852 := by exact prefixLift 5451852
  have htrace : WordTrace (prefixWord ++ tailWord_5451852) baseStart_5451852 baseEnd_5451852 := by
    simpa [prefixWord, tailWord_5451852, baseEnd_5451852] using wordTrace_append hprefix tailTrace_5451852
  have hstable : (prefixWord ++ tailWord_5451852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451852).length < 2 ^ (prefixWord ++ tailWord_5451852).sum := by decide
  have hdescent : baseEnd_5451852 < baseStart_5451852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451869 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5451869 : Nat := 118140960795 + 5451869 * 2 ^ 59
def prefixEnd_5451869 : Nat := 4983230072969 + 3 ^ 40 * 5451869 * 2
def baseEnd_5451869 : Nat := 933143087449011757054939

theorem tailTrace_5451869 : CollatzResearch.WordTrace tailWord_5451869 prefixEnd_5451869 933143087449011757054939 := by
  unfold tailWord_5451869
  simp only [CollatzResearch.WordTrace]
  refine ⟨198845998285817192941246661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132563998857211461960831107 198845998285817192941246661)
  ·
    refine ⟨37283624678590723676483749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198845998285817192941246661 37283624678590723676483749)
    ·
      refine ⟨6990679627235760689340703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37283624678590723676483749 6990679627235760689340703)
      ·
        refine ⟨10486019440853641034011055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990679627235760689340703 10486019440853641034011055)
        ·
          refine ⟨15729029161280461551016583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10486019440853641034011055 15729029161280461551016583)
          ·
            refine ⟨23593543741920692326524875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15729029161280461551016583 23593543741920692326524875)
            ·
              refine ⟨35390315612881038489787313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23593543741920692326524875 35390315612881038489787313)
              ·
                refine ⟨26542736709660778867340485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35390315612881038489787313 26542736709660778867340485)
                ·
                  refine ⟨4976763133061396037626341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26542736709660778867340485 4976763133061396037626341)
                  ·
                    refine ⟨933143087449011757054939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976763133061396037626341 933143087449011757054939)
                    ·
                      rfl

theorem cell23_5451869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5451869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451869 prefixEnd_5451869 := by exact prefixLift 5451869
  have htrace : WordTrace (prefixWord ++ tailWord_5451869) baseStart_5451869 baseEnd_5451869 := by
    simpa [prefixWord, tailWord_5451869, baseEnd_5451869] using wordTrace_append hprefix tailTrace_5451869
  have hstable : (prefixWord ++ tailWord_5451869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451869).length < 2 ^ (prefixWord ++ tailWord_5451869).sum := by decide
  have hdescent : baseEnd_5451869 < baseStart_5451869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451882 : List Nat := [3, 1, 3, 2, 3, 2, 9]
def baseStart_5451882 : Nat := 118140960795 + 5451882 * 2 ^ 59
def prefixEnd_5451882 : Nat := 4983230072969 + 3 ^ 40 * 5451882 * 2
def baseEnd_5451882 : Nat := 34560937501179552102497

theorem tailTrace_5451882 : CollatzResearch.WordTrace tailWord_5451882 prefixEnd_5451882 34560937501179552102497 := by
  unfold tailWord_5451882
  simp only [CollatzResearch.WordTrace]
  refine ⟨49711618108692524040367475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132564314956513397440979933 49711618108692524040367475)
  ·
    refine ⟨74567427163038786060551213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49711618108692524040367475 74567427163038786060551213)
    ·
      refine ⟨27962785186139544772706705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74567427163038786060551213 27962785186139544772706705)
      ·
        refine ⟨20972088889604658579530029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27962785186139544772706705 20972088889604658579530029)
        ·
          refine ⟨7864533333601746967323761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20972088889604658579530029 7864533333601746967323761)
          ·
            refine ⟨5898400000201310225492821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7864533333601746967323761 5898400000201310225492821)
            ·
              refine ⟨34560937501179552102497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5898400000201310225492821 34560937501179552102497)
              ·
                rfl

theorem cell23_5451882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 9].length) (baseStart_5451882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451882 prefixEnd_5451882 := by exact prefixLift 5451882
  have htrace : WordTrace (prefixWord ++ tailWord_5451882) baseStart_5451882 baseEnd_5451882 := by
    simpa [prefixWord, tailWord_5451882, baseEnd_5451882] using wordTrace_append hprefix tailTrace_5451882
  have hstable : (prefixWord ++ tailWord_5451882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451882).length < 2 ^ (prefixWord ++ tailWord_5451882).sum := by decide
  have hdescent : baseEnd_5451882 < baseStart_5451882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451943 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_5451943 : Nat := 118140960795 + 5451943 * 2 ^ 59
def prefixEnd_5451943 : Nat := 4983230072969 + 3 ^ 40 * 5451943 * 2
def baseEnd_5451943 : Nat := 2799467259915467981639477

theorem tailTrace_5451943 : CollatzResearch.WordTrace tailWord_5451943 prefixEnd_5451943 2799467259915467981639477 := by
  unfold tailWord_5451943
  simp only [CollatzResearch.WordTrace]
  refine ⟨198848697287549103579440483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132565798191699402386293655 198848697287549103579440483)
  ·
    refine ⟨298273045931323655369160725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198848697287549103579440483 298273045931323655369160725)
    ·
      refine ⟨13981549028030796345429409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 298273045931323655369160725 13981549028030796345429409)
      ·
        refine ⟨10486161771023097259072057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13981549028030796345429409 10486161771023097259072057)
        ·
          refine ⟨7864621328267322944304043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10486161771023097259072057 7864621328267322944304043)
          ·
            refine ⟨11796931992400984416456065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7864621328267322944304043 11796931992400984416456065)
            ·
              refine ⟨8847698994300738312342049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11796931992400984416456065 8847698994300738312342049)
              ·
                refine ⟨6635774245725553734256537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8847698994300738312342049 6635774245725553734256537)
                ·
                  refine ⟨4976830684294165300692403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6635774245725553734256537 4976830684294165300692403)
                  ·
                    refine ⟨7465246026441247951038605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976830684294165300692403 7465246026441247951038605)
                    ·
                      refine ⟨2799467259915467981639477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7465246026441247951038605 2799467259915467981639477)
                      ·
                        rfl

theorem cell23_5451943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_5451943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451943 prefixEnd_5451943 := by exact prefixLift 5451943
  have htrace : WordTrace (prefixWord ++ tailWord_5451943) baseStart_5451943 baseEnd_5451943 := by
    simpa [prefixWord, tailWord_5451943, baseEnd_5451943] using wordTrace_append hprefix tailTrace_5451943
  have hstable : (prefixWord ++ tailWord_5451943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451943).length < 2 ^ (prefixWord ++ tailWord_5451943).sum := by decide
  have hdescent : baseEnd_5451943 < baseStart_5451943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451955 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 7]
def baseStart_5451955 : Nat := 118140960795 + 5451955 * 2 ^ 59
def prefixEnd_5451955 : Nat := 4983230072969 + 3 ^ 40 * 5451955 * 2
def baseEnd_5451955 : Nat := 311052602409257992743269

theorem tailTrace_5451955 : CollatzResearch.WordTrace tailWord_5451955 prefixEnd_5451955 311052602409257992743269 := by
  unfold tailWord_5451955
  simp only [CollatzResearch.WordTrace]
  refine ⟨198849134963505629628877319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132566089975670419752584879 198849134963505629628877319)
  ·
    refine ⟨298273702445258444443315979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198849134963505629628877319 298273702445258444443315979)
    ·
      refine ⟨447410553667887666664973969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298273702445258444443315979 447410553667887666664973969)
      ·
        refine ⟨335557915250915749998730477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447410553667887666664973969 335557915250915749998730477)
        ·
          refine ⟨125834218219093406249523929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335557915250915749998730477 125834218219093406249523929)
          ·
            refine ⟨94375663664320054687142947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125834218219093406249523929 94375663664320054687142947)
            ·
              refine ⟨141563495496480082030714421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94375663664320054687142947 141563495496480082030714421)
              ·
                refine ⟨13271577702795007690379477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141563495496480082030714421 13271577702795007690379477)
                ·
                  refine ⟨311052602409257992743269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13271577702795007690379477 311052602409257992743269)
                  ·
                    rfl

theorem cell23_5451955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 7].length) (baseStart_5451955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451955 prefixEnd_5451955 := by exact prefixLift 5451955
  have htrace : WordTrace (prefixWord ++ tailWord_5451955) baseStart_5451955 baseEnd_5451955 := by
    simpa [prefixWord, tailWord_5451955, baseEnd_5451955] using wordTrace_append hprefix tailTrace_5451955
  have hstable : (prefixWord ++ tailWord_5451955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451955).length < 2 ^ (prefixWord ++ tailWord_5451955).sum := by decide
  have hdescent : baseEnd_5451955 < baseStart_5451955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451972 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 9]
def baseStart_5451972 : Nat := 118140960795 + 5451972 * 2 ^ 59
def prefixEnd_5451972 : Nat := 4983230072969 + 3 ^ 40 * 5451972 * 2
def baseEnd_5451972 : Nat := 311053572317160929797427

theorem tailTrace_5451972 : CollatzResearch.WordTrace tailWord_5451972 prefixEnd_5451972 311053572317160929797427 := by
  unfold tailWord_5451972
  simp only [CollatzResearch.WordTrace]
  refine ⟨99424877502222020766123085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132566503336296027688164113 99424877502222020766123085)
  ·
    refine ⟨37284329063333257787296157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99424877502222020766123085 37284329063333257787296157)
    ·
      refine ⟨13981623398749971670236059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37284329063333257787296157 13981623398749971670236059)
      ·
        refine ⟨20972435098124957505354089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13981623398749971670236059 20972435098124957505354089)
        ·
          refine ⟨15729326323593718129015567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20972435098124957505354089 15729326323593718129015567)
          ·
            refine ⟨23593989485390577193523351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15729326323593718129015567 23593989485390577193523351)
            ·
              refine ⟨35390984228085865790285027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23593989485390577193523351 35390984228085865790285027)
              ·
                refine ⟨53086476342128798685427541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35390984228085865790285027 53086476342128798685427541)
                ·
                  refine ⟨311053572317160929797427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53086476342128798685427541 311053572317160929797427)
                  ·
                    rfl

theorem cell23_5451972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_5451972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451972 prefixEnd_5451972 := by exact prefixLift 5451972
  have htrace : WordTrace (prefixWord ++ tailWord_5451972) baseStart_5451972 baseEnd_5451972 := by
    simpa [prefixWord, tailWord_5451972, baseEnd_5451972] using wordTrace_append hprefix tailTrace_5451972
  have hstable : (prefixWord ++ tailWord_5451972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451972).length < 2 ^ (prefixWord ++ tailWord_5451972).sum := by decide
  have hdescent : baseEnd_5451972 < baseStart_5451972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452066 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_5452066 : Nat := 118140960795 + 5452066 * 2 ^ 59
def prefixEnd_5452066 : Nat := 4983230072969 + 3 ^ 40 * 5452066 * 2
def baseEnd_5452066 : Nat := 933176806011990333467137

theorem tailTrace_5452066 : CollatzResearch.WordTrace tailWord_5452066 prefixEnd_5452066 933176806011990333467137 := by
  unfold tailWord_5452066
  simp only [CollatzResearch.WordTrace]
  refine ⟨49713295866525873896542013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132568788977402330390778701 49713295866525873896542013)
  ·
    refine ⟨18642485949947202711203255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49713295866525873896542013 18642485949947202711203255)
    ·
      refine ⟨27963728924920804066804883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18642485949947202711203255 27963728924920804066804883)
      ·
        refine ⟨41945593387381206100207325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27963728924920804066804883 41945593387381206100207325)
        ·
          refine ⟨15729597520267952287577747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41945593387381206100207325 15729597520267952287577747)
          ·
            refine ⟨23594396280401928431366621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15729597520267952287577747 23594396280401928431366621)
            ·
              refine ⟨8847898605150723161762483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23594396280401928431366621 8847898605150723161762483)
              ·
                refine ⟨13271847907726084742643725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8847898605150723161762483 13271847907726084742643725)
                ·
                  refine ⟨4976942965397281778491397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13271847907726084742643725 4976942965397281778491397)
                  ·
                    refine ⟨933176806011990333467137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976942965397281778491397 933176806011990333467137)
                    ·
                      rfl

theorem cell23_5452066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_5452066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452066 prefixEnd_5452066 := by exact prefixLift 5452066
  have htrace : WordTrace (prefixWord ++ tailWord_5452066) baseStart_5452066 baseEnd_5452066 := by
    simpa [prefixWord, tailWord_5452066, baseEnd_5452066] using wordTrace_append hprefix tailTrace_5452066
  have hstable : (prefixWord ++ tailWord_5452066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452066).length < 2 ^ (prefixWord ++ tailWord_5452066).sum := by decide
  have hdescent : baseEnd_5452066 < baseStart_5452066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452079 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 6]
def baseStart_5452079 : Nat := 118140960795 + 5452079 * 2 ^ 59
def prefixEnd_5452079 : Nat := 4983230072969 + 3 ^ 40 * 5452079 * 2
def baseEnd_5452079 : Nat := 311059677031608827726539

theorem tailTrace_5452079 : CollatzResearch.WordTrace tailWord_5452079 prefixEnd_5452079 311059677031608827726539 := by
  unfold tailWord_5452079
  simp only [CollatzResearch.WordTrace]
  refine ⟨198853657615056398806391291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132569105076704265870927527 198853657615056398806391291)
  ·
    refine ⟨298280486422584598209586937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198853657615056398806391291 298280486422584598209586937)
    ·
      refine ⟨223710364816938448657190203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298280486422584598209586937 223710364816938448657190203)
      ·
        refine ⟨335565547225407672985785305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223710364816938448657190203 335565547225407672985785305)
        ·
          refine ⟨251674160419055754739338979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335565547225407672985785305 251674160419055754739338979)
          ·
            refine ⟨377511240628583632109008469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251674160419055754739338979 377511240628583632109008469)
            ·
              refine ⟨4423959851116214438777443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 377511240628583632109008469 4423959851116214438777443)
              ·
                refine ⟨6635939776674321658166165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423959851116214438777443 6635939776674321658166165)
                ·
                  refine ⟨311059677031608827726539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6635939776674321658166165 311059677031608827726539)
                  ·
                    rfl

theorem cell23_5452079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 6].length) (baseStart_5452079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452079 prefixEnd_5452079 := by exact prefixLift 5452079
  have htrace : WordTrace (prefixWord ++ tailWord_5452079) baseStart_5452079 baseEnd_5452079 := by
    simpa [prefixWord, tailWord_5452079, baseEnd_5452079] using wordTrace_append hprefix tailTrace_5452079
  have hstable : (prefixWord ++ tailWord_5452079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452079).length < 2 ^ (prefixWord ++ tailWord_5452079).sum := by decide
  have hdescent : baseEnd_5452079 < baseStart_5452079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452099 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 1, 5, 2]
def baseStart_5452099 : Nat := 118140960795 + 5452099 * 2 ^ 59
def prefixEnd_5452099 : Nat := 4983230072969 + 3 ^ 40 * 5452099 * 2
def baseEnd_5452099 : Nat := 2799547362897569371288759

theorem tailTrace_5452099 : CollatzResearch.WordTrace tailWord_5452099 prefixEnd_5452099 2799547362897569371288759 := by
  unfold tailWord_5452099
  simp only [CollatzResearch.WordTrace]
  refine ⟨198854387074983942222119351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132569591383322628148079567 198854387074983942222119351)
  ·
    refine ⟨298281580612475913333179027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198854387074983942222119351 298281580612475913333179027)
    ·
      refine ⟨447422370918713869999768541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298281580612475913333179027 447422370918713869999768541)
      ·
        refine ⟨167783389094517701249913203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447422370918713869999768541 167783389094517701249913203)
        ·
          refine ⟨251675083641776551874869805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167783389094517701249913203 251675083641776551874869805)
          ·
            refine ⟨94378156365666206953076177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251675083641776551874869805 94378156365666206953076177)
            ·
              refine ⟨70783617274249655214807133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94378156365666206953076177 70783617274249655214807133)
              ·
                refine ⟨26543856477843620705552675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70783617274249655214807133 26543856477843620705552675)
                ·
                  refine ⟨39815784716765431058329013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26543856477843620705552675 39815784716765431058329013)
                  ·
                    refine ⟨3732729817196759161718345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39815784716765431058329013 3732729817196759161718345)
                    ·
                      refine ⟨2799547362897569371288759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732729817196759161718345 2799547362897569371288759)
                      ·
                        rfl

theorem cell23_5452099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_5452099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452099 prefixEnd_5452099 := by exact prefixLift 5452099
  have htrace : WordTrace (prefixWord ++ tailWord_5452099) baseStart_5452099 baseEnd_5452099 := by
    simpa [prefixWord, tailWord_5452099, baseEnd_5452099] using wordTrace_append hprefix tailTrace_5452099
  have hstable : (prefixWord ++ tailWord_5452099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452099).length < 2 ^ (prefixWord ++ tailWord_5452099).sum := by decide
  have hdescent : baseEnd_5452099 < baseStart_5452099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452117 : List Nat := [1, 3, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_5452117 : Nat := 118140960795 + 5452117 * 2 ^ 59
def prefixEnd_5452117 : Nat := 4983230072969 + 3 ^ 40 * 5452117 * 2
def baseEnd_5452117 : Nat := 933185535183116766954559

theorem tailTrace_5452117 : CollatzResearch.WordTrace tailWord_5452117 prefixEnd_5452117 933185535183116766954559 := by
  unfold tailWord_5452117
  simp only [CollatzResearch.WordTrace]
  refine ⟨198855043588918731296274605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132570029059279154197516403 198855043588918731296274605)
  ·
    refine ⟨74570641345844524236102977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198855043588918731296274605 74570641345844524236102977)
    ·
      refine ⟨55927981009383393177077233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74570641345844524236102977 55927981009383393177077233)
      ·
        refine ⟨41945985757037544882807925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55927981009383393177077233 41945985757037544882807925)
        ·
          refine ⟨3932436164722269832763243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41945985757037544882807925 3932436164722269832763243)
          ·
            refine ⟨5898654247083404749144865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932436164722269832763243 5898654247083404749144865)
            ·
              refine ⟨4423990685312553561858649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5898654247083404749144865 4423990685312553561858649)
              ·
                refine ⟨3317993013984415171393987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4423990685312553561858649 3317993013984415171393987)
                ·
                  refine ⟨4976989520976622757090981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317993013984415171393987 4976989520976622757090981)
                  ·
                    refine ⟨933185535183116766954559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976989520976622757090981 933185535183116766954559)
                    ·
                      rfl

theorem cell23_5452117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_5452117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452117 prefixEnd_5452117 := by exact prefixLift 5452117
  have htrace : WordTrace (prefixWord ++ tailWord_5452117) baseStart_5452117 baseEnd_5452117 := by
    simpa [prefixWord, tailWord_5452117, baseEnd_5452117] using wordTrace_append hprefix tailTrace_5452117
  have hstable : (prefixWord ++ tailWord_5452117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452117).length < 2 ^ (prefixWord ++ tailWord_5452117).sum := by decide
  have hdescent : baseEnd_5452117 < baseStart_5452117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452122 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_5452122 : Nat := 118140960795 + 5452122 * 2 ^ 59
def prefixEnd_5452122 : Nat := 4983230072969 + 3 ^ 40 * 5452122 * 2
def baseEnd_5452122 : Nat := 933186390984207593767051

theorem tailTrace_5452122 : CollatzResearch.WordTrace tailWord_5452122 prefixEnd_5452122 933186390984207593767051 := by
  unfold tailWord_5452122
  simp only [CollatzResearch.WordTrace]
  refine ⟨49713806488475154287551655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132570150635933744766804413 49713806488475154287551655)
  ·
    refine ⟨74570709732712731431327483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49713806488475154287551655 74570709732712731431327483)
    ·
      refine ⟨111856064599069097146991225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74570709732712731431327483 111856064599069097146991225)
      ·
        refine ⟨83892048449301822860243419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111856064599069097146991225 83892048449301822860243419)
        ·
          refine ⟨125838072673952734290365129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83892048449301822860243419 125838072673952734290365129)
          ·
            refine ⟨94378554505464550717773847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125838072673952734290365129 94378554505464550717773847)
            ·
              refine ⟨141567831758196826076660771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94378554505464550717773847 141567831758196826076660771)
              ·
                refine ⟨212351747637295239114991157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141567831758196826076660771 212351747637295239114991157)
                ·
                  refine ⟨19907976340996428667030421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212351747637295239114991157 19907976340996428667030421)
                  ·
                    refine ⟨933186390984207593767051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19907976340996428667030421 933186390984207593767051)
                    ·
                      rfl

theorem cell23_5452122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_5452122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452122 prefixEnd_5452122 := by exact prefixLift 5452122
  have htrace : WordTrace (prefixWord ++ tailWord_5452122) baseStart_5452122 baseEnd_5452122 := by
    simpa [prefixWord, tailWord_5452122, baseEnd_5452122] using wordTrace_append hprefix tailTrace_5452122
  have hstable : (prefixWord ++ tailWord_5452122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452122).length < 2 ^ (prefixWord ++ tailWord_5452122).sum := by decide
  have hdescent : baseEnd_5452122 < baseStart_5452122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452129 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_5452129 : Nat := 118140960795 + 5452129 * 2 ^ 59
def prefixEnd_5452129 : Nat := 4983230072969 + 3 ^ 40 * 5452129 * 2
def baseEnd_5452129 : Nat := 2799562767317204253913621

theorem tailTrace_5452129 : CollatzResearch.WordTrace tailWord_5452129 prefixEnd_5452129 2799562767317204253913621 := by
  unfold tailWord_5452129
  simp only [CollatzResearch.WordTrace]
  refine ⟨198855481264875257345711441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132570320843250171563807627 198855481264875257345711441)
  ·
    refine ⟨149141610948656443009283581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198855481264875257345711441 149141610948656443009283581)
    ·
      refine ⟨55928104105746166128481343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149141610948656443009283581 55928104105746166128481343)
      ·
        refine ⟨83892156158619249192722015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55928104105746166128481343 83892156158619249192722015)
        ·
          refine ⟨125838234237928873789083023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83892156158619249192722015 125838234237928873789083023)
          ·
            refine ⟨188757351356893310683624535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125838234237928873789083023 188757351356893310683624535)
            ·
              refine ⟨283136027035339966025436803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188757351356893310683624535 283136027035339966025436803)
              ·
                refine ⟨424704040553009949038155205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283136027035339966025436803 424704040553009949038155205)
                ·
                  refine ⟨79632007603689365444654101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 424704040553009949038155205 79632007603689365444654101)
                  ·
                    refine ⟨3732750356422939005218161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79632007603689365444654101 3732750356422939005218161)
                    ·
                      refine ⟨2799562767317204253913621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732750356422939005218161 2799562767317204253913621)
                      ·
                        rfl

theorem cell23_5452129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_5452129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452129 prefixEnd_5452129 := by exact prefixLift 5452129
  have htrace : WordTrace (prefixWord ++ tailWord_5452129) baseStart_5452129 baseEnd_5452129 := by
    simpa [prefixWord, tailWord_5452129, baseEnd_5452129] using wordTrace_append hprefix tailTrace_5452129
  have hstable : (prefixWord ++ tailWord_5452129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452129).length < 2 ^ (prefixWord ++ tailWord_5452129).sum := by decide
  have hdescent : baseEnd_5452129 < baseStart_5452129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452150 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5452150 : Nat := 118140960795 + 5452150 * 2 ^ 59
def prefixEnd_5452150 : Nat := 4983230072969 + 3 ^ 40 * 5452150 * 2
def baseEnd_5452150 : Nat := 2799573550410948671751025

theorem tailTrace_5452150 : CollatzResearch.WordTrace tailWord_5452150 prefixEnd_5452150 2799573550410948671751025 := by
  unfold tailWord_5452150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12428515449862448620764119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132570831465199451954817269 12428515449862448620764119)
  ·
    refine ⟨18642773174793672931146179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12428515449862448620764119 18642773174793672931146179)
    ·
      refine ⟨27964159762190509396719269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18642773174793672931146179 27964159762190509396719269)
      ·
        refine ⟨5243279955410720511884863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27964159762190509396719269 5243279955410720511884863)
        ·
          refine ⟨7864919933116080767827295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5243279955410720511884863 7864919933116080767827295)
          ·
            refine ⟨11797379899674121151740943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7864919933116080767827295 11797379899674121151740943)
            ·
              refine ⟨17696069849511181727611415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11797379899674121151740943 17696069849511181727611415)
              ·
                refine ⟨26544104774266772591417123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17696069849511181727611415 26544104774266772591417123)
                ·
                  refine ⟨39816157161400158887125685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26544104774266772591417123 39816157161400158887125685)
                  ·
                    refine ⟨3732764733881264895668033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39816157161400158887125685 3732764733881264895668033)
                    ·
                      refine ⟨2799573550410948671751025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732764733881264895668033 2799573550410948671751025)
                      ·
                        rfl

theorem cell23_5452150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5452150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452150 prefixEnd_5452150 := by exact prefixLift 5452150
  have htrace : WordTrace (prefixWord ++ tailWord_5452150) baseStart_5452150 baseEnd_5452150 := by
    simpa [prefixWord, tailWord_5452150, baseEnd_5452150] using wordTrace_append hprefix tailTrace_5452150
  have hstable : (prefixWord ++ tailWord_5452150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452150).length < 2 ^ (prefixWord ++ tailWord_5452150).sum := by decide
  have hdescent : baseEnd_5452150 < baseStart_5452150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452196 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_5452196 : Nat := 118140960795 + 5452196 * 2 ^ 59
def prefixEnd_5452196 : Nat := 4983230072969 + 3 ^ 40 * 5452196 * 2
def baseEnd_5452196 : Nat := 2799597170521055491775813

theorem tailTrace_5452196 : CollatzResearch.WordTrace tailWord_5452196 prefixEnd_5452196 2799597170521055491775813 := by
  unfold tailWord_5452196
  simp only [CollatzResearch.WordTrace]
  refine ⟨99428962477816263894200221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132571949970421685192266961 99428962477816263894200221)
  ·
    refine ⟨37285860929181098960325083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99428962477816263894200221 37285860929181098960325083)
    ·
      refine ⟨55928791393771648440487625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37285860929181098960325083 55928791393771648440487625)
      ·
        refine ⟨41946593545328736330365719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55928791393771648440487625 41946593545328736330365719)
        ·
          refine ⟨62919890317993104495548579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41946593545328736330365719 62919890317993104495548579)
          ·
            refine ⟨94379835476989656743322869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62919890317993104495548579 94379835476989656743322869)
            ·
              refine ⟨8848109575967780319686519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94379835476989656743322869 8848109575967780319686519)
              ·
                refine ⟨13272164363951670479529779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8848109575967780319686519 13272164363951670479529779)
                ·
                  refine ⟨19908246545927505719294669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13272164363951670479529779 19908246545927505719294669)
                  ·
                    refine ⟨7465592454722814644735501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19908246545927505719294669 7465592454722814644735501)
                    ·
                      refine ⟨2799597170521055491775813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7465592454722814644735501 2799597170521055491775813)
                      ·
                        rfl

theorem cell23_5452196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_5452196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452196 prefixEnd_5452196 := by exact prefixLift 5452196
  have htrace : WordTrace (prefixWord ++ tailWord_5452196) baseStart_5452196 baseEnd_5452196 := by
    simpa [prefixWord, tailWord_5452196, baseEnd_5452196] using wordTrace_append hprefix tailTrace_5452196
  have hstable : (prefixWord ++ tailWord_5452196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452196).length < 2 ^ (prefixWord ++ tailWord_5452196).sum := by decide
  have hdescent : baseEnd_5452196 < baseStart_5452196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452200 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5452200 : Nat := 118140960795 + 5452200 * 2 ^ 59
def prefixEnd_5452200 : Nat := 4983230072969 + 3 ^ 40 * 5452200 * 2
def baseEnd_5452200 : Nat := 2799599224443673476125795

theorem tailTrace_5452200 : CollatzResearch.WordTrace tailWord_5452200 prefixEnd_5452200 2799599224443673476125795 := by
  unfold tailWord_5452200
  simp only [CollatzResearch.WordTrace]
  refine ⟨99429035423809018235773027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132572047231745357647697369 99429035423809018235773027)
  ·
    refine ⟨149143553135713527353659541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99429035423809018235773027 149143553135713527353659541)
    ·
      refine ⟨6991104053236571594702791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149143553135713527353659541 6991104053236571594702791)
      ·
        refine ⟨10486656079854857392054187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6991104053236571594702791 10486656079854857392054187)
        ·
          refine ⟨15729984119782286088081281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10486656079854857392054187 15729984119782286088081281)
          ·
            refine ⟨11797488089836714566060961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15729984119782286088081281 11797488089836714566060961)
            ·
              refine ⟨8848116067377535924545721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11797488089836714566060961 8848116067377535924545721)
              ·
                refine ⟨6636087050533151943409291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8848116067377535924545721 6636087050533151943409291)
                ·
                  refine ⟨9954130575799727915113937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6636087050533151943409291 9954130575799727915113937)
                  ·
                    refine ⟨7465597931849795936335453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9954130575799727915113937 7465597931849795936335453)
                    ·
                      refine ⟨2799599224443673476125795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7465597931849795936335453 2799599224443673476125795)
                      ·
                        rfl

theorem cell23_5452200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5452200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452200 prefixEnd_5452200 := by exact prefixLift 5452200
  have htrace : WordTrace (prefixWord ++ tailWord_5452200) baseStart_5452200 baseEnd_5452200 := by
    simpa [prefixWord, tailWord_5452200, baseEnd_5452200] using wordTrace_append hprefix tailTrace_5452200
  have hstable : (prefixWord ++ tailWord_5452200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452200).length < 2 ^ (prefixWord ++ tailWord_5452200).sum := by decide
  have hdescent : baseEnd_5452200 < baseStart_5452200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452209 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_5452209 : Nat := 118140960795 + 5452209 * 2 ^ 59
def prefixEnd_5452209 : Nat := 4983230072969 + 3 ^ 40 * 5452209 * 2
def baseEnd_5452209 : Nat := 2799603845769563940913253

theorem tailTrace_5452209 : CollatzResearch.WordTrace tailWord_5452209 prefixEnd_5452209 2799603845769563940913253 := by
  unfold tailWord_5452209
  simp only [CollatzResearch.WordTrace]
  refine ⟨198858399104585431008623681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132572266069723620672415787 198858399104585431008623681)
  ·
    refine ⟨149143799328439073256467761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198858399104585431008623681 149143799328439073256467761)
    ·
      refine ⟨111857849496329304942350821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149143799328439073256467761 111857849496329304942350821)
      ·
        refine ⟨20973346780561744676690779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111857849496329304942350821 20973346780561744676690779)
        ·
          refine ⟨31460020170842617015036169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20973346780561744676690779 31460020170842617015036169)
          ·
            refine ⟨23595015128131962761277127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31460020170842617015036169 23595015128131962761277127)
            ·
              refine ⟨35392522692197944141915691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23595015128131962761277127 35392522692197944141915691)
              ·
                refine ⟨53088784038296916212873537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35392522692197944141915691 53088784038296916212873537)
                ·
                  refine ⟨39816588028722687159655153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53088784038296916212873537 39816588028722687159655153)
                  ·
                    refine ⟨29862441021542015369741365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39816588028722687159655153 29862441021542015369741365)
                    ·
                      refine ⟨2799603845769563940913253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29862441021542015369741365 2799603845769563940913253)
                      ·
                        rfl

theorem cell23_5452209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_5452209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452209 prefixEnd_5452209 := by exact prefixLift 5452209
  have htrace : WordTrace (prefixWord ++ tailWord_5452209) baseStart_5452209 baseEnd_5452209 := by
    simpa [prefixWord, tailWord_5452209, baseEnd_5452209] using wordTrace_append hprefix tailTrace_5452209
  have hstable : (prefixWord ++ tailWord_5452209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452209).length < 2 ^ (prefixWord ++ tailWord_5452209).sum := by decide
  have hdescent : baseEnd_5452209 < baseStart_5452209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452239 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 3]
def baseStart_5452239 : Nat := 118140960795 + 5452239 * 2 ^ 59
def prefixEnd_5452239 : Nat := 4983230072969 + 3 ^ 40 * 5452239 * 2
def baseEnd_5452239 : Nat := 2799619250189198823538115

theorem tailTrace_5452239 : CollatzResearch.WordTrace tailWord_5452239 prefixEnd_5452239 2799619250189198823538115 := by
  unfold tailWord_5452239
  simp only [CollatzResearch.WordTrace]
  refine ⟨198859493294476746132215771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132572995529651164088143847 198859493294476746132215771)
  ·
    refine ⟨298289239941715119198323657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198859493294476746132215771 298289239941715119198323657)
    ·
      refine ⟨223716929956286339398742743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298289239941715119198323657 223716929956286339398742743)
      ·
        refine ⟨335575394934429509098114115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223716929956286339398742743 335575394934429509098114115)
        ·
          refine ⟨503363092401644263647171173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335575394934429509098114115 503363092401644263647171173)
          ·
            refine ⟨94380579825308299433844595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 503363092401644263647171173 94380579825308299433844595)
            ·
              refine ⟨141570869737962449150766893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94380579825308299433844595 141570869737962449150766893)
              ·
                refine ⟨53089076151735918431537585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141570869737962449150766893 53089076151735918431537585)
                ·
                  refine ⟨39816807113801938823653189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53089076151735918431537585 39816807113801938823653189)
                  ·
                    refine ⟨7465651333837863529434973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39816807113801938823653189 7465651333837863529434973)
                    ·
                      refine ⟨2799619250189198823538115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7465651333837863529434973 2799619250189198823538115)
                      ·
                        rfl

theorem cell23_5452239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_5452239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452239 prefixEnd_5452239 := by exact prefixLift 5452239
  have htrace : WordTrace (prefixWord ++ tailWord_5452239) baseStart_5452239 baseEnd_5452239 := by
    simpa [prefixWord, tailWord_5452239, baseEnd_5452239] using wordTrace_append hprefix tailTrace_5452239
  have hstable : (prefixWord ++ tailWord_5452239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452239).length < 2 ^ (prefixWord ++ tailWord_5452239).sum := by decide
  have hdescent : baseEnd_5452239 < baseStart_5452239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452246 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5452246 : Nat := 118140960795 + 5452246 * 2 ^ 59
def prefixEnd_5452246 : Nat := 4983230072969 + 3 ^ 40 * 5452246 * 2
def baseEnd_5452246 : Nat := 933207614851260098716861

theorem tailTrace_5452246 : CollatzResearch.WordTrace tailWord_5452246 prefixEnd_5452246 933207614851260098716861 := by
  unfold tailWord_5452246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12428734287840711645482537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132573165736967590885147061 12428734287840711645482537)
  ·
    refine ⟨9321550715880533734111903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12428734287840711645482537 9321550715880533734111903)
    ·
      refine ⟨13982326073820800601167855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9321550715880533734111903 13982326073820800601167855)
      ·
        refine ⟨20973489110731200901751783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13982326073820800601167855 20973489110731200901751783)
        ·
          refine ⟨31460233666096801352627675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20973489110731200901751783 31460233666096801352627675)
          ·
            refine ⟨47190350499145202028941513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31460233666096801352627675 47190350499145202028941513)
            ·
              refine ⟨35392762874358901521706135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47190350499145202028941513 35392762874358901521706135)
              ·
                refine ⟨53089144311538352282559203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35392762874358901521706135 53089144311538352282559203)
                ·
                  refine ⟨79633716467307528423838805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53089144311538352282559203 79633716467307528423838805)
                  ·
                    refine ⟨933207614851260098716861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79633716467307528423838805 933207614851260098716861)
                    ·
                      rfl

theorem cell23_5452246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5452246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452246 prefixEnd_5452246 := by exact prefixLift 5452246
  have htrace : WordTrace (prefixWord ++ tailWord_5452246) baseStart_5452246 baseEnd_5452246 := by
    simpa [prefixWord, tailWord_5452246, baseEnd_5452246] using wordTrace_append hprefix tailTrace_5452246
  have hstable : (prefixWord ++ tailWord_5452246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452246).length < 2 ^ (prefixWord ++ tailWord_5452246).sum := by decide
  have hdescent : baseEnd_5452246 < baseStart_5452246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452249 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_5452249 : Nat := 118140960795 + 5452249 * 2 ^ 59
def prefixEnd_5452249 : Nat := 4983230072969 + 3 ^ 40 * 5452249 * 2
def baseEnd_5452249 : Nat := 2799624384995743784413069

theorem tailTrace_5452249 : CollatzResearch.WordTrace tailWord_5452249 prefixEnd_5452249 2799624384995743784413069 := by
  unfold tailWord_5452249
  simp only [CollatzResearch.WordTrace]
  refine ⟨198859858024440517840079801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132573238682960345226719867 198859858024440517840079801)
  ·
    refine ⟨149144893518330388380059851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198859858024440517840079801 149144893518330388380059851)
    ·
      refine ⟨223717340277495582570089777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149144893518330388380059851 223717340277495582570089777)
      ·
        refine ⟨167788005208121686927567333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223717340277495582570089777 167788005208121686927567333)
        ·
          refine ⟨31460250976522816298918875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167788005208121686927567333 31460250976522816298918875)
          ·
            refine ⟨47190376464784224448378313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31460250976522816298918875 47190376464784224448378313)
            ·
              refine ⟨35392782348588168336283735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47190376464784224448378313 35392782348588168336283735)
              ·
                refine ⟨53089173522882252504425603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35392782348588168336283735 53089173522882252504425603)
                ·
                  refine ⟨79633760284323378756638405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53089173522882252504425603 79633760284323378756638405)
                  ·
                    refine ⟨14931330053310633516869701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79633760284323378756638405 14931330053310633516869701)
                    ·
                      refine ⟨2799624384995743784413069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14931330053310633516869701 2799624384995743784413069)
                      ·
                        rfl

theorem cell23_5452249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_5452249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452249 prefixEnd_5452249 := by exact prefixLift 5452249
  have htrace : WordTrace (prefixWord ++ tailWord_5452249) baseStart_5452249 baseEnd_5452249 := by
    simpa [prefixWord, tailWord_5452249, baseEnd_5452249] using wordTrace_append hprefix tailTrace_5452249
  have hstable : (prefixWord ++ tailWord_5452249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452249).length < 2 ^ (prefixWord ++ tailWord_5452249).sum := by decide
  have hdescent : baseEnd_5452249 < baseStart_5452249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452253 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_5452253 : Nat := 118140960795 + 5452253 * 2 ^ 59
def prefixEnd_5452253 : Nat := 4983230072969 + 3 ^ 40 * 5452253 * 2
def baseEnd_5452253 : Nat := 2799626438918361768763051

theorem tailTrace_5452253 : CollatzResearch.WordTrace tailWord_5452253 prefixEnd_5452253 2799626438918361768763051 := by
  unfold tailWord_5452253
  simp only [CollatzResearch.WordTrace]
  refine ⟨198860003916426026523225413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132573335944284017682150275 198860003916426026523225413)
  ·
    refine ⟨37286250734329879973104765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198860003916426026523225413 37286250734329879973104765)
    ·
      refine ⟨13982344025373704989914287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37286250734329879973104765 13982344025373704989914287)
      ·
        refine ⟨20973516038060557484871431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13982344025373704989914287 20973516038060557484871431)
        ·
          refine ⟨31460274057090836227307147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20973516038060557484871431 31460274057090836227307147)
          ·
            refine ⟨47190411085636254340960721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31460274057090836227307147 47190411085636254340960721)
            ·
              refine ⟨35392808314227190755720541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47190411085636254340960721 35392808314227190755720541)
              ·
                refine ⟨13272303117835196533395203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35392808314227190755720541 13272303117835196533395203)
                ·
                  refine ⟨19908454676752794800092805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13272303117835196533395203 19908454676752794800092805)
                  ·
                    refine ⟨3732835251891149025017401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19908454676752794800092805 3732835251891149025017401)
                    ·
                      refine ⟨2799626438918361768763051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732835251891149025017401 2799626438918361768763051)
                      ·
                        rfl

theorem cell23_5452253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_5452253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452253 prefixEnd_5452253 := by exact prefixLift 5452253
  have htrace : WordTrace (prefixWord ++ tailWord_5452253) baseStart_5452253 baseEnd_5452253 := by
    simpa [prefixWord, tailWord_5452253, baseEnd_5452253] using wordTrace_append hprefix tailTrace_5452253
  have hstable : (prefixWord ++ tailWord_5452253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452253).length < 2 ^ (prefixWord ++ tailWord_5452253).sum := by decide
  have hdescent : baseEnd_5452253 < baseStart_5452253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452293 : List Nat := [1, 3, 1, 1, 2, 2, 6, 2, 5]
def baseStart_5452293 : Nat := 118140960795 + 5452293 * 2 ^ 59
def prefixEnd_5452293 : Nat := 4983230072969 + 3 ^ 40 * 5452293 * 2
def baseEnd_5452293 : Nat := 311071886460504623584763

theorem tailTrace_5452293 : CollatzResearch.WordTrace tailWord_5452293 prefixEnd_5452293 311071886460504623584763 := by
  unfold tailWord_5452293
  simp only [CollatzResearch.WordTrace]
  refine ⟨198861462836281113354681533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132574308557520742236454355 198861462836281113354681533)
  ·
    refine ⟨74573048563605417508005575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198861462836281113354681533 74573048563605417508005575)
    ·
      refine ⟨111859572845408126262008363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74573048563605417508005575 111859572845408126262008363)
      ·
        refine ⟨167789359268112189393012545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111859572845408126262008363 167789359268112189393012545)
        ·
          refine ⟨125842019451084142044759409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167789359268112189393012545 125842019451084142044759409)
          ·
            refine ⟨94381514588313106533569557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125842019451084142044759409 94381514588313106533569557)
            ·
              refine ⟨4424133496327176868761073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94381514588313106533569557 4424133496327176868761073)
              ·
                refine ⟨3318100122245382651570805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424133496327176868761073 3318100122245382651570805)
                ·
                  refine ⟨311071886460504623584763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3318100122245382651570805 311071886460504623584763)
                  ·
                    rfl

theorem cell23_5452293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_5452293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452293 prefixEnd_5452293 := by exact prefixLift 5452293
  have htrace : WordTrace (prefixWord ++ tailWord_5452293) baseStart_5452293 baseEnd_5452293 := by
    simpa [prefixWord, tailWord_5452293, baseEnd_5452293] using wordTrace_append hprefix tailTrace_5452293
  have hstable : (prefixWord ++ tailWord_5452293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452293).length < 2 ^ (prefixWord ++ tailWord_5452293).sum := by decide
  have hdescent : baseEnd_5452293 < baseStart_5452293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452323 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 2, 5]
def baseStart_5452323 : Nat := 118140960795 + 5452323 * 2 ^ 59
def prefixEnd_5452323 : Nat := 4983230072969 + 3 ^ 40 * 5452323 * 2
def baseEnd_5452323 : Nat := 933220794188058831629243

theorem tailTrace_5452323 : CollatzResearch.WordTrace tailWord_5452323 prefixEnd_5452323 933220794188058831629243 := by
  unfold tailWord_5452323
  simp only [CollatzResearch.WordTrace]
  refine ⟨198862557026172428478273623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132575038017448285652182415 198862557026172428478273623)
  ·
    refine ⟨298293835539258642717410435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198862557026172428478273623 298293835539258642717410435)
    ·
      refine ⟨447440753308887964076115653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298293835539258642717410435 447440753308887964076115653)
      ·
        refine ⟨83895141245416493264271685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 447440753308887964076115653 83895141245416493264271685)
        ·
          refine ⟨15730338983515592487050941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83895141245416493264271685 15730338983515592487050941)
          ·
            refine ⟨5898877118818347182644103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15730338983515592487050941 5898877118818347182644103)
            ·
              refine ⟨8848315678227520773966155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898877118818347182644103 8848315678227520773966155)
              ·
                refine ⟨13272473517341281160949233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8848315678227520773966155 13272473517341281160949233)
                ·
                  refine ⟨9954355138005960870711925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13272473517341281160949233 9954355138005960870711925)
                  ·
                    refine ⟨933220794188058831629243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9954355138005960870711925 933220794188058831629243)
                    ·
                      rfl

theorem cell23_5452323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 5].length) (baseStart_5452323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452323 prefixEnd_5452323 := by exact prefixLift 5452323
  have htrace : WordTrace (prefixWord ++ tailWord_5452323) baseStart_5452323 baseEnd_5452323 := by
    simpa [prefixWord, tailWord_5452323, baseEnd_5452323] using wordTrace_append hprefix tailTrace_5452323
  have hstable : (prefixWord ++ tailWord_5452323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452323).length < 2 ^ (prefixWord ++ tailWord_5452323).sum := by decide
  have hdescent : baseEnd_5452323 < baseStart_5452323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452327 : List Nat := [1, 1, 7, 2, 1, 1, 2, 3, 5]
def baseStart_5452327 : Nat := 118140960795 + 5452327 * 2 ^ 59
def prefixEnd_5452327 : Nat := 4983230072969 + 3 ^ 40 * 5452327 * 2
def baseEnd_5452327 : Nat := 311073826276310497693079

theorem tailTrace_5452327 : CollatzResearch.WordTrace tailWord_5452327 prefixEnd_5452327 311073826276310497693079 := by
  unfold tailWord_5452327
  simp only [CollatzResearch.WordTrace]
  refine ⟨198862702918157937161419235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132575135278771958107612823 198862702918157937161419235)
  ·
    refine ⟨298294054377236905742128853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198862702918157937161419235 298294054377236905742128853)
    ·
      refine ⟨6991266899466489978331145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 298294054377236905742128853 6991266899466489978331145)
      ·
        refine ⟨5243450174599867483748359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6991266899466489978331145 5243450174599867483748359)
        ·
          refine ⟨7865175261899801225622539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5243450174599867483748359 7865175261899801225622539)
          ·
            refine ⟨11797762892849701838433809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7865175261899801225622539 11797762892849701838433809)
            ·
              refine ⟨8848322169637276378825357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11797762892849701838433809 8848322169637276378825357)
              ·
                refine ⟨3318120813613978642059509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8848322169637276378825357 3318120813613978642059509)
                ·
                  refine ⟨311073826276310497693079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3318120813613978642059509 311073826276310497693079)
                  ·
                    rfl

theorem cell23_5452327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 5].length) (baseStart_5452327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452327 prefixEnd_5452327 := by exact prefixLift 5452327
  have htrace : WordTrace (prefixWord ++ tailWord_5452327) baseStart_5452327 baseEnd_5452327 := by
    simpa [prefixWord, tailWord_5452327, baseEnd_5452327] using wordTrace_append hprefix tailTrace_5452327
  have hstable : (prefixWord ++ tailWord_5452327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452327).length < 2 ^ (prefixWord ++ tailWord_5452327).sum := by decide
  have hdescent : baseEnd_5452327 < baseStart_5452327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452339 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 6]
def baseStart_5452339 : Nat := 118140960795 + 5452339 * 2 ^ 59
def prefixEnd_5452339 : Nat := 4983230072969 + 3 ^ 40 * 5452339 * 2
def baseEnd_5452339 : Nat := 2799670598254648432287655

theorem tailTrace_5452339 : CollatzResearch.WordTrace tailWord_5452339 prefixEnd_5452339 2799670598254648432287655 := by
  unfold tailWord_5452339
  simp only [CollatzResearch.WordTrace]
  refine ⟨198863140594114463210856071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132575427062742975473904047 198863140594114463210856071)
  ·
    refine ⟨298294710891171694816284107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198863140594114463210856071 298294710891171694816284107)
    ·
      refine ⟨447442066336757542224426161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298294710891171694816284107 447442066336757542224426161)
      ·
        refine ⟨335581549752568156668319621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447442066336757542224426161 335581549752568156668319621)
        ·
          refine ⟨62921540578606529375309929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335581549752568156668319621 62921540578606529375309929)
          ·
            refine ⟨47191155433954897031482447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62921540578606529375309929 47191155433954897031482447)
            ·
              refine ⟨70786733150932345547223671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47191155433954897031482447 70786733150932345547223671)
              ·
                refine ⟨106180099726398518320835507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70786733150932345547223671 106180099726398518320835507)
                ·
                  refine ⟨159270149589597777481253261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106180099726398518320835507 159270149589597777481253261)
                  ·
                    refine ⟨59726306096099166555469973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159270149589597777481253261 59726306096099166555469973)
                    ·
                      refine ⟨2799670598254648432287655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59726306096099166555469973 2799670598254648432287655)
                      ·
                        rfl

theorem cell23_5452339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_5452339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452339 prefixEnd_5452339 := by exact prefixLift 5452339
  have htrace : WordTrace (prefixWord ++ tailWord_5452339) baseStart_5452339 baseEnd_5452339 := by
    simpa [prefixWord, tailWord_5452339, baseEnd_5452339] using wordTrace_append hprefix tailTrace_5452339
  have hstable : (prefixWord ++ tailWord_5452339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452339).length < 2 ^ (prefixWord ++ tailWord_5452339).sum := by decide
  have hdescent : baseEnd_5452339 < baseStart_5452339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452353 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 3, 4]
def baseStart_5452353 : Nat := 118140960795 + 5452353 * 2 ^ 59
def prefixEnd_5452353 : Nat := 4983230072969 + 3 ^ 40 * 5452353 * 2
def baseEnd_5452353 : Nat := 933225928994603792504197

theorem tailTrace_5452353 : CollatzResearch.WordTrace tailWord_5452353 prefixEnd_5452353 933225928994603792504197 := by
  unfold tailWord_5452353
  simp only [CollatzResearch.WordTrace]
  refine ⟨198863651216063743601865713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132575767477375829067910475 198863651216063743601865713)
  ·
    refine ⟨149147738412047807701399285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198863651216063743601865713 149147738412047807701399285)
    ·
      refine ⟨13982600476129481972006183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149147738412047807701399285 13982600476129481972006183)
      ·
        refine ⟨20973900714194222958009275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13982600476129481972006183 20973900714194222958009275)
        ·
          refine ⟨31460851071291334437013913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20973900714194222958009275 31460851071291334437013913)
          ·
            refine ⟨23595638303468500827760435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31460851071291334437013913 23595638303468500827760435)
            ·
              refine ⟨35393457455202751241640653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23595638303468500827760435 35393457455202751241640653)
              ·
                refine ⟨13272546545701031715615245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35393457455202751241640653 13272546545701031715615245)
                ·
                  refine ⟨4977204954637886893355717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13272546545701031715615245 4977204954637886893355717)
                  ·
                    refine ⟨933225928994603792504197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977204954637886893355717 933225928994603792504197)
                    ·
                      rfl

theorem cell23_5452353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_5452353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452353 prefixEnd_5452353 := by exact prefixLift 5452353
  have htrace : WordTrace (prefixWord ++ tailWord_5452353) baseStart_5452353 baseEnd_5452353 := by
    simpa [prefixWord, tailWord_5452353, baseEnd_5452353] using wordTrace_append hprefix tailTrace_5452353
  have hstable : (prefixWord ++ tailWord_5452353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452353).length < 2 ^ (prefixWord ++ tailWord_5452353).sum := by decide
  have hdescent : baseEnd_5452353 < baseStart_5452353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452366 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_5452366 : Nat := 118140960795 + 5452366 * 2 ^ 59
def prefixEnd_5452366 : Nat := 4983230072969 + 3 ^ 40 * 5452366 * 2
def baseEnd_5452366 : Nat := 311076051359146647405559

theorem tailTrace_5452366 : CollatzResearch.WordTrace tailWord_5452366 prefixEnd_5452366 311076051359146647405559 := by
  unfold tailWord_5452366
  simp only [CollatzResearch.WordTrace]
  refine ⟨24858015670627080852761119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132576083576677764548059301 24858015670627080852761119)
  ·
    refine ⟨37287023505940621279141679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24858015670627080852761119 37287023505940621279141679)
    ·
      refine ⟨55930535258910931918712519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37287023505940621279141679 55930535258910931918712519)
      ·
        refine ⟨83895802888366397878068779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55930535258910931918712519 83895802888366397878068779)
        ·
          refine ⟨125843704332549596817103169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83895802888366397878068779 125843704332549596817103169)
          ·
            refine ⟨94382778249412197612827377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125843704332549596817103169 94382778249412197612827377)
            ·
              refine ⟨70787083687059148209620533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94382778249412197612827377 70787083687059148209620533)
              ·
                refine ⟨6636289095661795144651925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70787083687059148209620533 6636289095661795144651925)
                ·
                  refine ⟨311076051359146647405559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6636289095661795144651925 311076051359146647405559)
                  ·
                    rfl

theorem cell23_5452366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_5452366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452366 prefixEnd_5452366 := by exact prefixLift 5452366
  have htrace : WordTrace (prefixWord ++ tailWord_5452366) baseStart_5452366 baseEnd_5452366 := by
    simpa [prefixWord, tailWord_5452366, baseEnd_5452366] using wordTrace_append hprefix tailTrace_5452366
  have hstable : (prefixWord ++ tailWord_5452366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452366).length < 2 ^ (prefixWord ++ tailWord_5452366).sum := by decide
  have hdescent : baseEnd_5452366 < baseStart_5452366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452461 : List Nat := [1, 5, 2, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_5452461 : Nat := 118140960795 + 5452461 * 2 ^ 59
def prefixEnd_5452461 : Nat := 4983230072969 + 3 ^ 40 * 5452461 * 2
def baseEnd_5452461 : Nat := 2799733242894496954962095

theorem tailTrace_5452461 : CollatzResearch.WordTrace tailWord_5452461 prefixEnd_5452461 2799733242894496954962095 := by
  unfold tailWord_5452461
  simp only [CollatzResearch.WordTrace]
  refine ⟨198867590299672478046797237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132578393533114985364531491 198867590299672478046797237)
  ·
    refine ⟨18643836590594294816887241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198867590299672478046797237 18643836590594294816887241)
    ·
      refine ⟨13982877442945721112665431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18643836590594294816887241 13982877442945721112665431)
      ·
        refine ⟨20974316164418581668998147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13982877442945721112665431 20974316164418581668998147)
        ·
          refine ⟨31461474246627872503497221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20974316164418581668998147 31461474246627872503497221)
          ·
            refine ⟨5899026421242726094405729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31461474246627872503497221 5899026421242726094405729)
            ·
              refine ⟨4424269815932044570804297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5899026421242726094405729 4424269815932044570804297)
              ·
                refine ⟨3318202361949033428103223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424269815932044570804297 3318202361949033428103223)
                ·
                  refine ⟨4977303542923550142154835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318202361949033428103223 4977303542923550142154835)
                  ·
                    refine ⟨7465955314385325213232253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4977303542923550142154835 7465955314385325213232253)
                    ·
                      refine ⟨2799733242894496954962095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7465955314385325213232253 2799733242894496954962095)
                      ·
                        rfl

theorem cell23_5452461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_5452461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452461 prefixEnd_5452461 := by exact prefixLift 5452461
  have htrace : WordTrace (prefixWord ++ tailWord_5452461) baseStart_5452461 baseEnd_5452461 := by
    simpa [prefixWord, tailWord_5452461, baseEnd_5452461] using wordTrace_append hprefix tailTrace_5452461
  have hstable : (prefixWord ++ tailWord_5452461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452461).length < 2 ^ (prefixWord ++ tailWord_5452461).sum := by decide
  have hdescent : baseEnd_5452461 < baseStart_5452461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452501 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5452501 : Nat := 118140960795 + 5452501 * 2 ^ 59
def prefixEnd_5452501 : Nat := 4983230072969 + 3 ^ 40 * 5452501 * 2
def baseEnd_5452501 : Nat := 2799753782120676798461911

theorem tailTrace_5452501 : CollatzResearch.WordTrace tailWord_5452501 prefixEnd_5452501 2799753782120676798461911 := by
  unfold tailWord_5452501
  simp only [CollatzResearch.WordTrace]
  refine ⟨198869049219527564878253357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132579366146351709918835571 198869049219527564878253357)
  ·
    refine ⟨74575893457322836829345009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198869049219527564878253357 74575893457322836829345009)
    ·
      refine ⟨55931920092992127622008757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74575893457322836829345009 55931920092992127622008757)
      ·
        refine ⟨5243617508718011964563321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55931920092992127622008757 5243617508718011964563321)
        ·
          refine ⟨3932713131538508973422491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5243617508718011964563321 3932713131538508973422491)
          ·
            refine ⟨5899069697307763460133737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932713131538508973422491 5899069697307763460133737)
            ·
              refine ⟨4424302272980822595100303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5899069697307763460133737 4424302272980822595100303)
              ·
                refine ⟨6636453409471233892650455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4424302272980822595100303 6636453409471233892650455)
                ·
                  refine ⟨9954680114206850838975683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6636453409471233892650455 9954680114206850838975683)
                  ·
                    refine ⟨14932020171310276258463525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9954680114206850838975683 14932020171310276258463525)
                    ·
                      refine ⟨2799753782120676798461911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14932020171310276258463525 2799753782120676798461911)
                      ·
                        rfl

theorem cell23_5452501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5452501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452501 prefixEnd_5452501 := by exact prefixLift 5452501
  have htrace : WordTrace (prefixWord ++ tailWord_5452501) baseStart_5452501 baseEnd_5452501 := by
    simpa [prefixWord, tailWord_5452501, baseEnd_5452501] using wordTrace_append hprefix tailTrace_5452501
  have hstable : (prefixWord ++ tailWord_5452501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452501).length < 2 ^ (prefixWord ++ tailWord_5452501).sum := by decide
  have hdescent : baseEnd_5452501 < baseStart_5452501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452517 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_5452517 : Nat := 118140960795 + 5452517 * 2 ^ 59
def prefixEnd_5452517 : Nat := 4983230072969 + 3 ^ 40 * 5452517 * 2
def baseEnd_5452517 : Nat := 2799761997811148735861837

theorem tailTrace_5452517 : CollatzResearch.WordTrace tailWord_5452517 prefixEnd_5452517 2799761997811148735861837 := by
  unfold tailWord_5452517
  simp only [CollatzResearch.WordTrace]
  refine ⟨198869632787469599610835805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132579755191646399740557203 198869632787469599610835805)
  ·
    refine ⟨74576112295301099854063427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198869632787469599610835805 74576112295301099854063427)
    ·
      refine ⟨111864168442951649781095141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74576112295301099854063427 111864168442951649781095141)
      ·
        refine ⟨20974531583053434333955339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111864168442951649781095141 20974531583053434333955339)
        ·
          refine ⟨31461797374580151500933009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20974531583053434333955339 31461797374580151500933009)
          ·
            refine ⟨23596348030935113625699757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31461797374580151500933009 23596348030935113625699757)
            ·
              refine ⟨8848630511600667609637409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23596348030935113625699757 8848630511600667609637409)
              ·
                refine ⟨6636472883700500707228057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8848630511600667609637409 6636472883700500707228057)
                ·
                  refine ⟨4977354662775375530421043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6636472883700500707228057 4977354662775375530421043)
                  ·
                    refine ⟨7466031994163063295631565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4977354662775375530421043 7466031994163063295631565)
                    ·
                      refine ⟨2799761997811148735861837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7466031994163063295631565 2799761997811148735861837)
                      ·
                        rfl

theorem cell23_5452517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_5452517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452517 prefixEnd_5452517 := by exact prefixLift 5452517
  have htrace : WordTrace (prefixWord ++ tailWord_5452517) baseStart_5452517 baseEnd_5452517 := by
    simpa [prefixWord, tailWord_5452517, baseEnd_5452517] using wordTrace_append hprefix tailTrace_5452517
  have hstable : (prefixWord ++ tailWord_5452517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452517).length < 2 ^ (prefixWord ++ tailWord_5452517).sum := by decide
  have hdescent : baseEnd_5452517 < baseStart_5452517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452534 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_5452534 : Nat := 118140960795 + 5452534 * 2 ^ 59
def prefixEnd_5452534 : Nat := 4983230072969 + 3 ^ 40 * 5452534 * 2
def baseEnd_5452534 : Nat := 2799770726982275169349259

theorem tailTrace_5452534 : CollatzResearch.WordTrace tailWord_5452534 prefixEnd_5452534 2799770726982275169349259 := by
  unfold tailWord_5452534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12429390801775500719637791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132580168552272007676136437 12429390801775500719637791)
  ·
    refine ⟨18644086202663251079456687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12429390801775500719637791 18644086202663251079456687)
    ·
      refine ⟨27966129303994876619185031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18644086202663251079456687 27966129303994876619185031)
      ·
        refine ⟨41949193955992314928777547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27966129303994876619185031 41949193955992314928777547)
        ·
          refine ⟨62923790933988472393166321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41949193955992314928777547 62923790933988472393166321)
          ·
            refine ⟨47192843200491354294874741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62923790933988472393166321 47192843200491354294874741)
            ·
              refine ⟨4424329050046064465144507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47192843200491354294874741 4424329050046064465144507)
              ·
                refine ⟨6636493575069096697716761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4424329050046064465144507 6636493575069096697716761)
                ·
                  refine ⟨4977370181301822523287571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6636493575069096697716761 4977370181301822523287571)
                  ·
                    refine ⟨7466055271952733784931357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4977370181301822523287571 7466055271952733784931357)
                    ·
                      refine ⟨2799770726982275169349259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7466055271952733784931357 2799770726982275169349259)
                      ·
                        rfl

theorem cell23_5452534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_5452534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452534 prefixEnd_5452534 := by exact prefixLift 5452534
  have htrace : WordTrace (prefixWord ++ tailWord_5452534) baseStart_5452534 baseEnd_5452534 := by
    simpa [prefixWord, tailWord_5452534, baseEnd_5452534] using wordTrace_append hprefix tailTrace_5452534
  have hstable : (prefixWord ++ tailWord_5452534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452534).length < 2 ^ (prefixWord ++ tailWord_5452534).sum := by decide
  have hdescent : baseEnd_5452534 < baseStart_5452534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452593 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 4, 5]
def baseStart_5452593 : Nat := 118140960795 + 5452593 * 2 ^ 59
def prefixEnd_5452593 : Nat := 4983230072969 + 3 ^ 40 * 5452593 * 2
def baseEnd_5452593 : Nat := 933267007446963479503829

theorem tailTrace_5452593 : CollatzResearch.WordTrace tailWord_5452593 prefixEnd_5452593 933267007446963479503829 := by
  unfold tailWord_5452593
  simp only [CollatzResearch.WordTrace]
  refine ⟨198872404735194264590602433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132581603156796176393734955 198872404735194264590602433)
  ·
    refine ⟨149154303551395698442951825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198872404735194264590602433 149154303551395698442951825)
    ·
      refine ⟨111865727663546773832213869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149154303551395698442951825 111865727663546773832213869)
      ·
        refine ⟨41949647873830040187080201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111865727663546773832213869 41949647873830040187080201)
        ·
          refine ⟨31462235905372530140310151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41949647873830040187080201 31462235905372530140310151)
          ·
            refine ⟨47193353858058795210465227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31462235905372530140310151 47193353858058795210465227)
            ·
              refine ⟨70790030787088192815697841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47193353858058795210465227 70790030787088192815697841)
              ·
                refine ⟨53092523090316144611773381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70790030787088192815697841 53092523090316144611773381)
                ·
                  refine ⟨9954848079434277114707509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53092523090316144611773381 9954848079434277114707509)
                  ·
                    refine ⟨933267007446963479503829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9954848079434277114707509 933267007446963479503829)
                    ·
                      rfl

theorem cell23_5452593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_5452593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452593 prefixEnd_5452593 := by exact prefixLift 5452593
  have htrace : WordTrace (prefixWord ++ tailWord_5452593) baseStart_5452593 baseEnd_5452593 := by
    simpa [prefixWord, tailWord_5452593, baseEnd_5452593] using wordTrace_append hprefix tailTrace_5452593
  have hstable : (prefixWord ++ tailWord_5452593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452593).length < 2 ^ (prefixWord ++ tailWord_5452593).sum := by decide
  have hdescent : baseEnd_5452593 < baseStart_5452593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452640 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 3, 4]
def baseStart_5452640 : Nat := 118140960795 + 5452640 * 2 ^ 59
def prefixEnd_5452640 : Nat := 4983230072969 + 3 ^ 40 * 5452640 * 2
def baseEnd_5452640 : Nat := 933275051977217251541257

theorem tailTrace_5452640 : CollatzResearch.WordTrace tailWord_5452640 prefixEnd_5452640 933275051977217251541257 := by
  unfold tailWord_5452640
  simp only [CollatzResearch.WordTrace]
  refine ⟨99437059483011995808781687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132582745977349327745042249 99437059483011995808781687)
  ·
    refine ⟨149155589224517993713172531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99437059483011995808781687 149155589224517993713172531)
    ·
      refine ⟨223733383836776990569758797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149155589224517993713172531 223733383836776990569758797)
      ·
        refine ⟨83900018938791371463659549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223733383836776990569758797 83900018938791371463659549)
        ·
          refine ⟨31462507102046764298872331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83900018938791371463659549 31462507102046764298872331)
          ·
            refine ⟨47193760653070146448308497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31462507102046764298872331 47193760653070146448308497)
            ·
              refine ⟨35395320489802609836231373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47193760653070146448308497 35395320489802609836231373)
              ·
                refine ⟨13273245183675978688586765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35395320489802609836231373 13273245183675978688586765)
                ·
                  refine ⟨4977466943878492008220037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13273245183675978688586765 4977466943878492008220037)
                  ·
                    refine ⟨933275051977217251541257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977466943878492008220037 933275051977217251541257)
                    ·
                      rfl

theorem cell23_5452640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 4].length) (baseStart_5452640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452640 prefixEnd_5452640 := by exact prefixLift 5452640
  have htrace : WordTrace (prefixWord ++ tailWord_5452640) baseStart_5452640 baseEnd_5452640 := by
    simpa [prefixWord, tailWord_5452640, baseEnd_5452640] using wordTrace_append hprefix tailTrace_5452640
  have hstable : (prefixWord ++ tailWord_5452640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452640).length < 2 ^ (prefixWord ++ tailWord_5452640).sum := by decide
  have hdescent : baseEnd_5452640 < baseStart_5452640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452647 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_5452647 : Nat := 118140960795 + 5452647 * 2 ^ 59
def prefixEnd_5452647 : Nat := 4983230072969 + 3 ^ 40 * 5452647 * 2
def baseEnd_5452647 : Nat := 2799828750296233227236239

theorem tailTrace_5452647 : CollatzResearch.WordTrace tailWord_5452647 prefixEnd_5452647 2799828750296233227236239 := by
  unfold tailWord_5452647
  simp only [CollatzResearch.WordTrace]
  refine ⟨198874374276998631813068195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132582916184665754542045463 198874374276998631813068195)
  ·
    refine ⟨298311561415497947719602293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198874374276998631813068195 298311561415497947719602293)
    ·
      refine ⟨27966708882702932598712715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 298311561415497947719602293 27966708882702932598712715)
      ·
        refine ⟨41950063324054398898069073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27966708882702932598712715 41950063324054398898069073)
        ·
          refine ⟨31462547493040799173551805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41950063324054398898069073 31462547493040799173551805)
          ·
            refine ⟨11798455309890299690081927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31462547493040799173551805 11798455309890299690081927)
            ·
              refine ⟨17697682964835449535122891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11798455309890299690081927 17697682964835449535122891)
              ·
                refine ⟨26546524447253174302684337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17697682964835449535122891 26546524447253174302684337)
                ·
                  refine ⟨19909893335439880727013253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26546524447253174302684337 19909893335439880727013253)
                  ·
                    refine ⟨3733105000394977636314985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19909893335439880727013253 3733105000394977636314985)
                    ·
                      refine ⟨2799828750296233227236239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733105000394977636314985 2799828750296233227236239)
                      ·
                        rfl

theorem cell23_5452647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_5452647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452647 prefixEnd_5452647 := by exact prefixLift 5452647
  have htrace : WordTrace (prefixWord ++ tailWord_5452647) baseStart_5452647 baseEnd_5452647 := by
    simpa [prefixWord, tailWord_5452647, baseEnd_5452647] using wordTrace_append hprefix tailTrace_5452647
  have hstable : (prefixWord ++ tailWord_5452647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452647).length < 2 ^ (prefixWord ++ tailWord_5452647).sum := by decide
  have hdescent : baseEnd_5452647 < baseStart_5452647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452653 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 10]
def baseStart_5452653 : Nat := 118140960795 + 5452653 * 2 ^ 59
def prefixEnd_5452653 : Nat := 4983230072969 + 3 ^ 40 * 5452653 * 2
def baseEnd_5452653 : Nat := 311092425686684467084579

theorem tailTrace_5452653 : CollatzResearch.WordTrace tailWord_5452653 prefixEnd_5452653 311092425686684467084579 := by
  unfold tailWord_5452653
  simp only [CollatzResearch.WordTrace]
  refine ⟨198874593114976894837786613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132583062076651263225191075 198874593114976894837786613)
  ·
    refine ⟨18644493104529083891042495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198874593114976894837786613 18644493104529083891042495)
    ·
      refine ⟨27966739656793625836563743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18644493104529083891042495 27966739656793625836563743)
      ·
        refine ⟨41950109485190438754845615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27966739656793625836563743 41950109485190438754845615)
        ·
          refine ⟨62925164227785658132268423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41950109485190438754845615 62925164227785658132268423)
          ·
            refine ⟨94387746341678487198402635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62925164227785658132268423 94387746341678487198402635)
            ·
              refine ⟨141581619512517730797603953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94387746341678487198402635 141581619512517730797603953)
              ·
                refine ⟨106186214634388298098202965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141581619512517730797603953 106186214634388298098202965)
                ·
                  refine ⟨311092425686684467084579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 106186214634388298098202965 311092425686684467084579)
                  ·
                    rfl

theorem cell23_5452653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_5452653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452653 prefixEnd_5452653 := by exact prefixLift 5452653
  have htrace : WordTrace (prefixWord ++ tailWord_5452653) baseStart_5452653 baseEnd_5452653 := by
    simpa [prefixWord, tailWord_5452653, baseEnd_5452653] using wordTrace_append hprefix tailTrace_5452653
  have hstable : (prefixWord ++ tailWord_5452653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452653).length < 2 ^ (prefixWord ++ tailWord_5452653).sum := by decide
  have hdescent : baseEnd_5452653 < baseStart_5452653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452730 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_5452730 : Nat := 118140960795 + 5452730 * 2 ^ 59
def prefixEnd_5452730 : Nat := 4983230072969 + 3 ^ 40 * 5452730 * 2
def baseEnd_5452730 : Nat := 933290456396852134166119

theorem tailTrace_5452730 : CollatzResearch.WordTrace tailWord_5452730 prefixEnd_5452730 933290456396852134166119 := by
  unfold tailWord_5452730
  simp only [CollatzResearch.WordTrace]
  refine ⟨49719350383924484247084911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132584934357131957992226429 49719350383924484247084911)
  ·
    refine ⟨74579025575886726370627367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49719350383924484247084911 74579025575886726370627367)
    ·
      refine ⟨111868538363830089555941051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74579025575886726370627367 111868538363830089555941051)
      ·
        refine ⟨167802807545745134333911577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111868538363830089555941051 167802807545745134333911577)
        ·
          refine ⟨125852105659308850750433683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167802807545745134333911577 125852105659308850750433683)
          ·
            refine ⟨188778158488963276125650525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125852105659308850750433683 188778158488963276125650525)
            ·
              refine ⟨70791809433361228547118947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188778158488963276125650525 70791809433361228547118947)
              ·
                refine ⟨106187714150041842820678421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70791809433361228547118947 106187714150041842820678421)
                ·
                  refine ⟨4977549100783211382219301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106187714150041842820678421 4977549100783211382219301)
                  ·
                    refine ⟨933290456396852134166119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977549100783211382219301 933290456396852134166119)
                    ·
                      rfl

theorem cell23_5452730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_5452730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452730 prefixEnd_5452730 := by exact prefixLift 5452730
  have htrace : WordTrace (prefixWord ++ tailWord_5452730) baseStart_5452730 baseEnd_5452730 := by
    simpa [prefixWord, tailWord_5452730, baseEnd_5452730] using wordTrace_append hprefix tailTrace_5452730
  have hstable : (prefixWord ++ tailWord_5452730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452730).length < 2 ^ (prefixWord ++ tailWord_5452730).sum := by decide
  have hdescent : baseEnd_5452730 < baseStart_5452730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452742 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_5452742 : Nat := 118140960795 + 5452742 * 2 ^ 59
def prefixEnd_5452742 : Nat := 4983230072969 + 3 ^ 40 * 5452742 * 2
def baseEnd_5452742 : Nat := 933292510319470118516101

theorem tailTrace_5452742 : CollatzResearch.WordTrace tailWord_5452742 prefixEnd_5452742 933292510319470118516101 := by
  unfold tailWord_5452742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214932475364201969930515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132585226141102975358517653 6214932475364201969930515)
  ·
    refine ⟨9322398713046302954895773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6214932475364201969930515 9322398713046302954895773)
    ·
      refine ⟨3495899517392363608085915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9322398713046302954895773 3495899517392363608085915)
      ·
        refine ⟨5243849276088545412128873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3495899517392363608085915 5243849276088545412128873)
        ·
          refine ⟨3932886957066409059096655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5243849276088545412128873 3932886957066409059096655)
          ·
            refine ⟨5899330435599613588644983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932886957066409059096655 5899330435599613588644983)
            ·
              refine ⟨8848995653399420382967475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5899330435599613588644983 8848995653399420382967475)
              ·
                refine ⟨13273493480099130574451213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8848995653399420382967475 13273493480099130574451213)
                ·
                  refine ⟨4977560055037173965419205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13273493480099130574451213 4977560055037173965419205)
                  ·
                    refine ⟨933292510319470118516101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977560055037173965419205 933292510319470118516101)
                    ·
                      rfl

theorem cell23_5452742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_5452742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452742 prefixEnd_5452742 := by exact prefixLift 5452742
  have htrace : WordTrace (prefixWord ++ tailWord_5452742) baseStart_5452742 baseEnd_5452742 := by
    simpa [prefixWord, tailWord_5452742, baseEnd_5452742] using wordTrace_append hprefix tailTrace_5452742
  have hstable : (prefixWord ++ tailWord_5452742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452742).length < 2 ^ (prefixWord ++ tailWord_5452742).sum := by decide
  have hdescent : baseEnd_5452742 < baseStart_5452742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452743 : List Nat := [1, 1, 4, 1, 1, 2, 13]
def baseStart_5452743 : Nat := 118140960795 + 5452743 * 2 ^ 59
def prefixEnd_5452743 : Nat := 4983230072969 + 3 ^ 40 * 5452743 * 2
def baseEnd_5452743 : Nat := 34566395610358825328837

theorem tailTrace_5452743 : CollatzResearch.WordTrace tailWord_5452743 prefixEnd_5452743 34566395610358825328837 := by
  unfold tailWord_5452743
  simp only [CollatzResearch.WordTrace]
  refine ⟨198877875684650840208562883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132585250456433893472375255 198877875684650840208562883)
  ·
    refine ⟨298316813526976260312844325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198877875684650840208562883 298316813526976260312844325)
    ·
      refine ⟨55934402536308048808658311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298316813526976260312844325 55934402536308048808658311)
      ·
        refine ⟨83901603804462073212987467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55934402536308048808658311 83901603804462073212987467)
        ·
          refine ⟨125852405706693109819481201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83901603804462073212987467 125852405706693109819481201)
          ·
            refine ⟨94389304280019832364610901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125852405706693109819481201 94389304280019832364610901)
            ·
              refine ⟨34566395610358825328837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 94389304280019832364610901 34566395610358825328837)
              ·
                rfl

theorem cell23_5452743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 13].length) (baseStart_5452743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452743 prefixEnd_5452743 := by exact prefixLift 5452743
  have htrace : WordTrace (prefixWord ++ tailWord_5452743) baseStart_5452743 baseEnd_5452743 := by
    simpa [prefixWord, tailWord_5452743, baseEnd_5452743] using wordTrace_append hprefix tailTrace_5452743
  have hstable : (prefixWord ++ tailWord_5452743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452743).length < 2 ^ (prefixWord ++ tailWord_5452743).sum := by decide
  have hdescent : baseEnd_5452743 < baseStart_5452743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452750 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_5452750 : Nat := 118140960795 + 5452750 * 2 ^ 59
def prefixEnd_5452750 : Nat := 4983230072969 + 3 ^ 40 * 5452750 * 2
def baseEnd_5452750 : Nat := 2799881638803646324248265

theorem tailTrace_5452750 : CollatzResearch.WordTrace tailWord_5452750 prefixEnd_5452750 2799881638803646324248265 := by
  unfold tailWord_5452750
  simp only [CollatzResearch.WordTrace]
  refine ⟨24859766374453185050508463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132585420663750320269378469 24859766374453185050508463)
  ·
    refine ⟨37289649561679777575762695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24859766374453185050508463 37289649561679777575762695)
    ·
      refine ⟨55934474342519666363644043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37289649561679777575762695 55934474342519666363644043)
      ·
        refine ⟨83901711513779499545466065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55934474342519666363644043 83901711513779499545466065)
        ·
          refine ⟨62926283635334624659099549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83901711513779499545466065 62926283635334624659099549)
          ·
            refine ⟨23597356363250484247162331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62926283635334624659099549 23597356363250484247162331)
            ·
              refine ⟨35396034544875726370743497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23597356363250484247162331 35396034544875726370743497)
              ·
                refine ⟨26547025908656794778057623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35396034544875726370743497 26547025908656794778057623)
                ·
                  refine ⟨39820538862985192167086435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26547025908656794778057623 39820538862985192167086435)
                  ·
                    refine ⟨59730808294477788250629653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39820538862985192167086435 59730808294477788250629653)
                    ·
                      refine ⟨2799881638803646324248265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59730808294477788250629653 2799881638803646324248265)
                      ·
                        rfl

theorem cell23_5452750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_5452750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452750 prefixEnd_5452750 := by exact prefixLift 5452750
  have htrace : WordTrace (prefixWord ++ tailWord_5452750) baseStart_5452750 baseEnd_5452750 := by
    simpa [prefixWord, tailWord_5452750, baseEnd_5452750] using wordTrace_append hprefix tailTrace_5452750
  have hstable : (prefixWord ++ tailWord_5452750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452750).length < 2 ^ (prefixWord ++ tailWord_5452750).sum := by decide
  have hdescent : baseEnd_5452750 < baseStart_5452750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452760 : List Nat := [2, 1, 2, 2, 2, 4, 2, 8]
def baseStart_5452760 : Nat := 118140960795 + 5452760 * 2 ^ 59
def prefixEnd_5452760 : Nat := 4983230072969 + 3 ^ 40 * 5452760 * 2
def baseEnd_5452760 : Nat := 103699510133710788337897

theorem tailTrace_5452760 : CollatzResearch.WordTrace tailWord_5452760 prefixEnd_5452760 103699510133710788337897 := by
  unfold tailWord_5452760
  simp only [CollatzResearch.WordTrace]
  refine ⟨99439247862794626055965867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132585663817059501407954489 99439247862794626055965867)
  ·
    refine ⟨149158871794191939083948801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99439247862794626055965867 149158871794191939083948801)
    ·
      refine ⟨111869153845643954312961601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149158871794191939083948801 111869153845643954312961601)
      ·
        refine ⟨83901865384232965734721201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111869153845643954312961601 83901865384232965734721201)
        ·
          refine ⟨62926399038174724301040901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83901865384232965734721201 62926399038174724301040901)
          ·
            refine ⟨11798699819657760806445169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62926399038174724301040901 11798699819657760806445169)
            ·
              refine ⟨8849024864743320604833877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11798699819657760806445169 8849024864743320604833877)
              ·
                refine ⟨103699510133710788337897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8849024864743320604833877 103699510133710788337897)
                ·
                  rfl

theorem cell23_5452760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 8].length) (baseStart_5452760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452760 prefixEnd_5452760 := by exact prefixLift 5452760
  have htrace : WordTrace (prefixWord ++ tailWord_5452760) baseStart_5452760 baseEnd_5452760 := by
    simpa [prefixWord, tailWord_5452760, baseEnd_5452760] using wordTrace_append hprefix tailTrace_5452760
  have hstable : (prefixWord ++ tailWord_5452760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452760).length < 2 ^ (prefixWord ++ tailWord_5452760).sum := by decide
  have hdescent : baseEnd_5452760 < baseStart_5452760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452814 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_5452814 : Nat := 118140960795 + 5452814 * 2 ^ 59
def prefixEnd_5452814 : Nat := 4983230072969 + 3 ^ 40 * 5452814 * 2
def baseEnd_5452814 : Nat := 2799914501565534073847971

theorem tailTrace_5452814 : CollatzResearch.WordTrace tailWord_5452814 prefixEnd_5452814 2799914501565534073847971 := by
  unfold tailWord_5452814
  simp only [CollatzResearch.WordTrace]
  refine ⟨24860058158424202416799687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132586976844929079556264997 24860058158424202416799687)
  ·
    refine ⟨37290087237636303625199531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24860058158424202416799687 37290087237636303625199531)
    ·
      refine ⟨55935130856454455437799297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37290087237636303625199531 55935130856454455437799297)
      ·
        refine ⟨41951348142340841578349473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55935130856454455437799297 41951348142340841578349473)
        ·
          refine ⟨31463511106755631183762105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41951348142340841578349473 31463511106755631183762105)
          ·
            refine ⟨23597633330066723387821579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31463511106755631183762105 23597633330066723387821579)
            ·
              refine ⟨35396449995100085081732369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23597633330066723387821579 35396449995100085081732369)
              ·
                refine ⟨26547337496325063811299277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35396449995100085081732369 26547337496325063811299277)
                ·
                  refine ⟨9955251561121898929237229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26547337496325063811299277 9955251561121898929237229)
                  ·
                    refine ⟨3733219335420712098463961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9955251561121898929237229 3733219335420712098463961)
                    ·
                      refine ⟨2799914501565534073847971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733219335420712098463961 2799914501565534073847971)
                      ·
                        rfl

theorem cell23_5452814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_5452814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452814 prefixEnd_5452814 := by exact prefixLift 5452814
  have htrace : WordTrace (prefixWord ++ tailWord_5452814) baseStart_5452814 baseEnd_5452814 := by
    simpa [prefixWord, tailWord_5452814, baseEnd_5452814] using wordTrace_append hprefix tailTrace_5452814
  have hstable : (prefixWord ++ tailWord_5452814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452814).length < 2 ^ (prefixWord ++ tailWord_5452814).sum := by decide
  have hdescent : baseEnd_5452814 < baseStart_5452814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452818 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5452818 : Nat := 118140960795 + 5452818 * 2 ^ 59
def prefixEnd_5452818 : Nat := 4983230072969 + 3 ^ 40 * 5452818 * 2
def baseEnd_5452818 : Nat := 2799916555488152058197953

theorem tailTrace_5452818 : CollatzResearch.WordTrace tailWord_5452818 prefixEnd_5452818 2799916555488152058197953 := by
  unfold tailWord_5452818
  simp only [CollatzResearch.WordTrace]
  refine ⟨49720152789844782004385777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132587074106252752011695405 49720152789844782004385777)
  ·
    refine ⟨37290114592383586503289333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49720152789844782004385777 37290114592383586503289333)
    ·
      refine ⟨3495948243035961234683375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37290114592383586503289333 3495948243035961234683375)
      ·
        refine ⟨5243922364553941852025063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3495948243035961234683375 5243922364553941852025063)
        ·
          refine ⟨7865883546830912778037595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5243922364553941852025063 7865883546830912778037595)
          ·
            refine ⟨11798825320246369167056393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7865883546830912778037595 11798825320246369167056393)
            ·
              refine ⟨8849118990184776875292295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11798825320246369167056393 8849118990184776875292295)
              ·
                refine ⟨13273678485277165312938443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8849118990184776875292295 13273678485277165312938443)
                ·
                  refine ⟨19910517727915747969407665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13273678485277165312938443 19910517727915747969407665)
                  ·
                    refine ⟨14932888295936810977055749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19910517727915747969407665 14932888295936810977055749)
                    ·
                      refine ⟨2799916555488152058197953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14932888295936810977055749 2799916555488152058197953)
                      ·
                        rfl

theorem cell23_5452818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5452818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452818 prefixEnd_5452818 := by exact prefixLift 5452818
  have htrace : WordTrace (prefixWord ++ tailWord_5452818) baseStart_5452818 baseEnd_5452818 := by
    simpa [prefixWord, tailWord_5452818, baseEnd_5452818] using wordTrace_append hprefix tailTrace_5452818
  have hstable : (prefixWord ++ tailWord_5452818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452818).length < 2 ^ (prefixWord ++ tailWord_5452818).sum := by decide
  have hdescent : baseEnd_5452818 < baseStart_5452818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452844 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 4, 2, 2]
def baseStart_5452844 : Nat := 118140960795 + 5452844 * 2 ^ 59
def prefixEnd_5452844 : Nat := 4983230072969 + 3 ^ 40 * 5452844 * 2
def baseEnd_5452844 : Nat := 2799929905985168956472833

theorem tailTrace_5452844 : CollatzResearch.WordTrace tailWord_5452844 prefixEnd_5452844 2799929905985168956472833 := by
  unfold tailWord_5452844
  simp only [CollatzResearch.WordTrace]
  refine ⟨99440779728642467228994793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132587706304856622971993057 99440779728642467228994793)
  ·
    refine ⟨74580584796481850421746095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99440779728642467228994793 74580584796481850421746095)
    ·
      refine ⟨111870877194722775632619143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74580584796481850421746095 111870877194722775632619143)
      ·
        refine ⟨167806315792084163448928715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111870877194722775632619143 167806315792084163448928715)
        ·
          refine ⟨251709473688126245173393073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167806315792084163448928715 251709473688126245173393073)
          ·
            refine ⟨188782105266094683880044805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251709473688126245173393073 188782105266094683880044805)
            ·
              refine ⟨35396644737392753227508401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188782105266094683880044805 35396644737392753227508401)
              ·
                refine ⟨26547483553044564920631301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35396644737392753227508401 26547483553044564920631301)
                ·
                  refine ⟨4977653166195855922618369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26547483553044564920631301 4977653166195855922618369)
                  ·
                    refine ⟨3733239874646891941963777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4977653166195855922618369 3733239874646891941963777)
                    ·
                      refine ⟨2799929905985168956472833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733239874646891941963777 2799929905985168956472833)
                      ·
                        rfl

theorem cell23_5452844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_5452844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452844 prefixEnd_5452844 := by exact prefixLift 5452844
  have htrace : WordTrace (prefixWord ++ tailWord_5452844) baseStart_5452844 baseEnd_5452844 := by
    simpa [prefixWord, tailWord_5452844, baseEnd_5452844] using wordTrace_append hprefix tailTrace_5452844
  have hstable : (prefixWord ++ tailWord_5452844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452844).length < 2 ^ (prefixWord ++ tailWord_5452844).sum := by decide
  have hdescent : baseEnd_5452844 < baseStart_5452844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452850 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 9]
def baseStart_5452850 : Nat := 118140960795 + 5452850 * 2 ^ 59
def prefixEnd_5452850 : Nat := 4983230072969 + 3 ^ 40 * 5452850 * 2
def baseEnd_5452850 : Nat := 311103665207677325888645

theorem tailTrace_5452850 : CollatzResearch.WordTrace tailWord_5452850 prefixEnd_5452850 311103665207677325888645 := by
  unfold tailWord_5452850
  simp only [CollatzResearch.WordTrace]
  refine ⟨49720444573815799370677001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132587852196842131655138669 49720444573815799370677001)
  ·
    refine ⟨37290333430361849528007751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49720444573815799370677001 37290333430361849528007751)
    ·
      refine ⟨55935500145542774292011627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37290333430361849528007751 55935500145542774292011627)
      ·
        refine ⟨83903250218314161438017441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55935500145542774292011627 83903250218314161438017441)
        ·
          refine ⟨62927437663735621078513081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83903250218314161438017441 62927437663735621078513081)
          ·
            refine ⟨47195578247801715808884811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62927437663735621078513081 47195578247801715808884811)
            ·
              refine ⟨70793367371702573713327217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47195578247801715808884811 70793367371702573713327217)
              ·
                refine ⟨53095025528776930284995413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70793367371702573713327217 53095025528776930284995413)
                ·
                  refine ⟨311103665207677325888645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53095025528776930284995413 311103665207677325888645)
                  ·
                    rfl

theorem cell23_5452850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_5452850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452850 prefixEnd_5452850 := by exact prefixLift 5452850
  have htrace : WordTrace (prefixWord ++ tailWord_5452850) baseStart_5452850 baseEnd_5452850 := by
    simpa [prefixWord, tailWord_5452850, baseEnd_5452850] using wordTrace_append hprefix tailTrace_5452850
  have hstable : (prefixWord ++ tailWord_5452850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452850).length < 2 ^ (prefixWord ++ tailWord_5452850).sum := by decide
  have hdescent : baseEnd_5452850 < baseStart_5452850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452857 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5452857 : Nat := 118140960795 + 5452857 * 2 ^ 59
def prefixEnd_5452857 : Nat := 4983230072969 + 3 ^ 40 * 5452857 * 2
def baseEnd_5452857 : Nat := 2799936581233677405610273

theorem tailTrace_5452857 : CollatzResearch.WordTrace tailWord_5452857 prefixEnd_5452857 2799936581233677405610273 := by
  unfold tailWord_5452857
  simp only [CollatzResearch.WordTrace]
  refine ⟨198882033606237837678212825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132588022404158558452141883 198882033606237837678212825)
  ·
    refine ⟨149161525204678378258659619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198882033606237837678212825 149161525204678378258659619)
    ·
      refine ⟨223742287807017567387989429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149161525204678378258659619 223742287807017567387989429)
      ·
        refine ⟨20975839481907896942624009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223742287807017567387989429 20975839481907896942624009)
        ·
          refine ⟨15731879611430922706968007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20975839481907896942624009 15731879611430922706968007)
          ·
            refine ⟨23597819417146384060452011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15731879611430922706968007 23597819417146384060452011)
            ·
              refine ⟨35396729125719576090678017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23597819417146384060452011 35396729125719576090678017)
              ·
                refine ⟨26547546844289682068008513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35396729125719576090678017 26547546844289682068008513)
                ·
                  refine ⟨19910660133217261551006385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26547546844289682068008513 19910660133217261551006385)
                  ·
                    refine ⟨14932995099912946163254789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19910660133217261551006385 14932995099912946163254789)
                    ·
                      refine ⟨2799936581233677405610273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14932995099912946163254789 2799936581233677405610273)
                      ·
                        rfl

theorem cell23_5452857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5452857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452857 prefixEnd_5452857 := by exact prefixLift 5452857
  have htrace : WordTrace (prefixWord ++ tailWord_5452857) baseStart_5452857 baseEnd_5452857 := by
    simpa [prefixWord, tailWord_5452857, baseEnd_5452857] using wordTrace_append hprefix tailTrace_5452857
  have hstable : (prefixWord ++ tailWord_5452857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452857).length < 2 ^ (prefixWord ++ tailWord_5452857).sum := by decide
  have hdescent : baseEnd_5452857 < baseStart_5452857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452861 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_5452861 : Nat := 118140960795 + 5452861 * 2 ^ 59
def prefixEnd_5452861 : Nat := 4983230072969 + 3 ^ 40 * 5452861 * 2
def baseEnd_5452861 : Nat := 2799938635156295389960255

theorem tailTrace_5452861 : CollatzResearch.WordTrace tailWord_5452861 prefixEnd_5452861 2799938635156295389960255 := by
  unfold tailWord_5452861
  simp only [CollatzResearch.WordTrace]
  refine ⟨198882179498223346361358437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132588119665482230907572291 198882179498223346361358437)
  ·
    refine ⟨37290408655916877442754707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198882179498223346361358437 37290408655916877442754707)
    ·
      refine ⟨55935612983875316164132061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37290408655916877442754707 55935612983875316164132061)
      ·
        refine ⟨20975854868953243561549523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55935612983875316164132061 20975854868953243561549523)
        ·
          refine ⟨31463782303429865342324285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20975854868953243561549523 31463782303429865342324285)
          ·
            refine ⟨11798918363786199503371607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31463782303429865342324285 11798918363786199503371607)
            ·
              refine ⟨17698377545679299255057411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11798918363786199503371607 17698377545679299255057411)
              ·
                refine ⟨26547566318518948882586117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17698377545679299255057411 26547566318518948882586117)
                ·
                  refine ⟨4977668684722302915484897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26547566318518948882586117 4977668684722302915484897)
                  ·
                    refine ⟨3733251513541727186613673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4977668684722302915484897 3733251513541727186613673)
                    ·
                      refine ⟨2799938635156295389960255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733251513541727186613673 2799938635156295389960255)
                      ·
                        rfl

theorem cell23_5452861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_5452861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452861 prefixEnd_5452861 := by exact prefixLift 5452861
  have htrace : WordTrace (prefixWord ++ tailWord_5452861) baseStart_5452861 baseEnd_5452861 := by
    simpa [prefixWord, tailWord_5452861, baseEnd_5452861] using wordTrace_append hprefix tailTrace_5452861
  have hstable : (prefixWord ++ tailWord_5452861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452861).length < 2 ^ (prefixWord ++ tailWord_5452861).sum := by decide
  have hdescent : baseEnd_5452861 < baseStart_5452861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452867 : List Nat := [1, 1, 1, 3, 1, 2, 3, 6, 5]
def baseStart_5452867 : Nat := 118140960795 + 5452867 * 2 ^ 59
def prefixEnd_5452867 : Nat := 4983230072969 + 3 ^ 40 * 5452867 * 2
def baseEnd_5452867 : Nat := 311104635115580262942803

theorem tailTrace_5452867 : CollatzResearch.WordTrace tailWord_5452867 prefixEnd_5452867 311104635115580262942803 := by
  unfold tailWord_5452867
  simp only [CollatzResearch.WordTrace]
  refine ⟨198882398336201609386076855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132588265557467739590717903 198882398336201609386076855)
  ·
    refine ⟨298323597504302414079115283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198882398336201609386076855 298323597504302414079115283)
    ·
      refine ⟨447485396256453621118672925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298323597504302414079115283 447485396256453621118672925)
      ·
        refine ⟨167807023596170107919502347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447485396256453621118672925 167807023596170107919502347)
        ·
          refine ⟨251710535394255161879253521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167807023596170107919502347 251710535394255161879253521)
          ·
            refine ⟨188782901545691371409440141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251710535394255161879253521 188782901545691371409440141)
            ·
              refine ⟨70793588079634264278540053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188782901545691371409440141 70793588079634264278540053)
              ·
                refine ⟨3318449441232856138056565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70793588079634264278540053 3318449441232856138056565)
                ·
                  refine ⟨311104635115580262942803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3318449441232856138056565 311104635115580262942803)
                  ·
                    rfl

theorem cell23_5452867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 5].length) (baseStart_5452867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452867 prefixEnd_5452867 := by exact prefixLift 5452867
  have htrace : WordTrace (prefixWord ++ tailWord_5452867) baseStart_5452867 baseEnd_5452867 := by
    simpa [prefixWord, tailWord_5452867, baseEnd_5452867] using wordTrace_append hprefix tailTrace_5452867
  have hstable : (prefixWord ++ tailWord_5452867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452867).length < 2 ^ (prefixWord ++ tailWord_5452867).sum := by decide
  have hdescent : baseEnd_5452867 < baseStart_5452867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452878 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_5452878 : Nat := 118140960795 + 5452878 * 2 ^ 59
def prefixEnd_5452878 : Nat := 4983230072969 + 3 ^ 40 * 5452878 * 2
def baseEnd_5452878 : Nat := 2799947364327421823447677

theorem tailTrace_5452878 : CollatzResearch.WordTrace tailWord_5452878 prefixEnd_5452878 2799947364327421823447677 := by
  unfold tailWord_5452878
  simp only [CollatzResearch.WordTrace]
  refine ⟨24860349942395219783090911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132588533026107838843151525 24860349942395219783090911)
  ·
    refine ⟨37290524913592829674636367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24860349942395219783090911 37290524913592829674636367)
    ·
      refine ⟨55935787370389244511954551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37290524913592829674636367 55935787370389244511954551)
      ·
        refine ⟨83903681055583866767931827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55935787370389244511954551 83903681055583866767931827)
        ·
          refine ⟨125855521583375800151897741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83903681055583866767931827 125855521583375800151897741)
          ·
            refine ⟨47195820593765925056961653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125855521583375800151897741 47195820593765925056961653)
            ·
              refine ⟨4424608180665555474090155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47195820593765925056961653 4424608180665555474090155)
              ·
                refine ⟨6636912270998333211135233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4424608180665555474090155 6636912270998333211135233)
                ·
                  refine ⟨4977684203248749908351425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6636912270998333211135233 4977684203248749908351425)
                  ·
                    refine ⟨3733263152436562431263569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4977684203248749908351425 3733263152436562431263569)
                    ·
                      refine ⟨2799947364327421823447677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733263152436562431263569 2799947364327421823447677)
                      ·
                        rfl

theorem cell23_5452878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_5452878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452878 prefixEnd_5452878 := by exact prefixLift 5452878
  have htrace : WordTrace (prefixWord ++ tailWord_5452878) baseStart_5452878 baseEnd_5452878 := by
    simpa [prefixWord, tailWord_5452878, baseEnd_5452878] using wordTrace_append hprefix tailTrace_5452878
  have hstable : (prefixWord ++ tailWord_5452878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452878).length < 2 ^ (prefixWord ++ tailWord_5452878).sum := by decide
  have hdescent : baseEnd_5452878 < baseStart_5452878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452890 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_5452890 : Nat := 118140960795 + 5452890 * 2 ^ 59
def prefixEnd_5452890 : Nat := 4983230072969 + 3 ^ 40 * 5452890 * 2
def baseEnd_5452890 : Nat := 2799953526095275776497621

theorem tailTrace_5452890 : CollatzResearch.WordTrace tailWord_5452890 prefixEnd_5452890 2799953526095275776497621 := by
  unfold tailWord_5452890
  simp only [CollatzResearch.WordTrace]
  refine ⟨49720809303779571078541031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132588824810078856209442749 49720809303779571078541031)
  ·
    refine ⟨74581213955669356617811547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49720809303779571078541031 74581213955669356617811547)
    ·
      refine ⟨111871820933504034926717321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74581213955669356617811547 111871820933504034926717321)
      ·
        refine ⟨83903865700128026195037991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111871820933504034926717321 83903865700128026195037991)
        ·
          refine ⟨125855798550192039292556987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83903865700128026195037991 125855798550192039292556987)
          ·
            refine ⟨188783697825288058938835481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125855798550192039292556987 188783697825288058938835481)
            ·
              refine ⟨141587773368966044204126611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188783697825288058938835481 141587773368966044204126611)
              ·
                refine ⟨212381660053449066306189917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141587773368966044204126611 212381660053449066306189917)
                ·
                  refine ⟨79643122520043399864821219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212381660053449066306189917 79643122520043399864821219)
                  ·
                    refine ⟨119464683780065099797231829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79643122520043399864821219 119464683780065099797231829)
                    ·
                      refine ⟨2799953526095275776497621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119464683780065099797231829 2799953526095275776497621)
                      ·
                        rfl

theorem cell23_5452890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_5452890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452890 prefixEnd_5452890 := by exact prefixLift 5452890
  have htrace : WordTrace (prefixWord ++ tailWord_5452890) baseStart_5452890 baseEnd_5452890 := by
    simpa [prefixWord, tailWord_5452890, baseEnd_5452890] using wordTrace_append hprefix tailTrace_5452890
  have hstable : (prefixWord ++ tailWord_5452890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452890).length < 2 ^ (prefixWord ++ tailWord_5452890).sum := by decide
  have hdescent : baseEnd_5452890 < baseStart_5452890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452961 : List Nat := [1, 2, 3, 3, 1, 1, 2, 5, 1, 4]
def baseStart_5452961 : Nat := 118140960795 + 5452961 * 2 ^ 59
def prefixEnd_5452961 : Nat := 4983230072969 + 3 ^ 40 * 5452961 * 2
def baseEnd_5452961 : Nat := 933329994407248332903265

theorem tailTrace_5452961 : CollatzResearch.WordTrace tailWord_5452961 prefixEnd_5452961 933329994407248332903265 := by
  unfold tailWord_5452961
  simp only [CollatzResearch.WordTrace]
  refine ⟨198885826797861063439998737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132590551198574042293332491 198885826797861063439998737)
  ·
    refine ⟨149164370098395797579999053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198885826797861063439998737 149164370098395797579999053)
    ·
      refine ⟨55936638786898424092499645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149164370098395797579999053 55936638786898424092499645)
      ·
        refine ⟨20976239545086909034687367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55936638786898424092499645 20976239545086909034687367)
        ·
          refine ⟨31464359317630363552031051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20976239545086909034687367 31464359317630363552031051)
          ·
            refine ⟨47196538976445545328046577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31464359317630363552031051 47196538976445545328046577)
            ·
              refine ⟨35397404232334158996034933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47196538976445545328046577 35397404232334158996034933)
              ·
                refine ⟨3318506646781327405878275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35397404232334158996034933 3318506646781327405878275)
                ·
                  refine ⟨4977759970171991108817413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318506646781327405878275 4977759970171991108817413)
                  ·
                    refine ⟨933329994407248332903265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977759970171991108817413 933329994407248332903265)
                    ·
                      rfl

theorem cell23_5452961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_5452961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452961 prefixEnd_5452961 := by exact prefixLift 5452961
  have htrace : WordTrace (prefixWord ++ tailWord_5452961) baseStart_5452961 baseEnd_5452961 := by
    simpa [prefixWord, tailWord_5452961, baseEnd_5452961] using wordTrace_append hprefix tailTrace_5452961
  have hstable : (prefixWord ++ tailWord_5452961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452961).length < 2 ^ (prefixWord ++ tailWord_5452961).sum := by decide
  have hdescent : baseEnd_5452961 < baseStart_5452961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5452978 : List Nat := [3, 2, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_5452978 : Nat := 118140960795 + 5452978 * 2 ^ 59
def prefixEnd_5452978 : Nat := 4983230072969 + 3 ^ 40 * 5452978 * 2
def baseEnd_5452978 : Nat := 933332904130957144065739

theorem tailTrace_5452978 : CollatzResearch.WordTrace tailWord_5452978 prefixEnd_5452978 933332904130957144065739 := by
  unfold tailWord_5452978
  simp only [CollatzResearch.WordTrace]
  refine ⟨49721611709699868835841897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132590964559199650228911725 49721611709699868835841897)
  ·
    refine ⟨37291208782274901626881423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49721611709699868835841897 37291208782274901626881423)
    ·
      refine ⟨55936813173412352440322135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37291208782274901626881423 55936813173412352440322135)
      ·
        refine ⟨83905219760118528660483203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55936813173412352440322135 83905219760118528660483203)
        ·
          refine ⟨125857829640177792990724805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83905219760118528660483203 125857829640177792990724805)
          ·
            refine ⟨23598343057533336185760901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125857829640177792990724805 23598343057533336185760901)
            ·
              refine ⟨4424689323287500534830169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23598343057533336185760901 4424689323287500534830169)
              ·
                refine ⟨3318516992465625401122627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424689323287500534830169 3318516992465625401122627)
                ·
                  refine ⟨4977775488698438101683941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318516992465625401122627 4977775488698438101683941)
                  ·
                    refine ⟨933332904130957144065739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977775488698438101683941 933332904130957144065739)
                    ·
                      rfl

theorem cell23_5452978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_5452978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5452978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5452978 prefixEnd_5452978 := by exact prefixLift 5452978
  have htrace : WordTrace (prefixWord ++ tailWord_5452978) baseStart_5452978 baseEnd_5452978 := by
    simpa [prefixWord, tailWord_5452978, baseEnd_5452978] using wordTrace_append hprefix tailTrace_5452978
  have hstable : (prefixWord ++ tailWord_5452978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5452978).length < 2 ^ (prefixWord ++ tailWord_5452978).sum := by decide
  have hdescent : baseEnd_5452978 < baseStart_5452978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5452978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453061 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_5453061 : Nat := 118140960795 + 5453061 * 2 ^ 59
def prefixEnd_5453061 : Nat := 4983230072969 + 3 ^ 40 * 5453061 * 2
def baseEnd_5453061 : Nat := 2800041331287194607459335

theorem tailTrace_5453061 : CollatzResearch.WordTrace tailWord_5453061 prefixEnd_5453061 2800041331287194607459335 := by
  unfold tailWord_5453061
  simp only [CollatzResearch.WordTrace]
  refine ⟨198889474097498780518639037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132592982731665853679092691 198889474097498780518639037)
  ·
    refine ⟨74583552786562042694489639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198889474097498780518639037 74583552786562042694489639)
    ·
      refine ⟨111875329179843064041734459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74583552786562042694489639 111875329179843064041734459)
      ·
        refine ⟨167812993769764596062601689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111875329179843064041734459 167812993769764596062601689)
        ·
          refine ⟨125859745327323447046951267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167812993769764596062601689 125859745327323447046951267)
          ·
            refine ⟨188789617990985170570426901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125859745327323447046951267 188789617990985170570426901)
            ·
              refine ⟨8849513343327429870488761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188789617990985170570426901 8849513343327429870488761)
              ·
                refine ⟨6637135007495572402866571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8849513343327429870488761 6637135007495572402866571)
                ·
                  refine ⟨9955702511243358604299857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6637135007495572402866571 9955702511243358604299857)
                  ·
                    refine ⟨7466776883432518953224893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9955702511243358604299857 7466776883432518953224893)
                    ·
                      refine ⟨2800041331287194607459335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7466776883432518953224893 2800041331287194607459335)
                      ·
                        rfl

theorem cell23_5453061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_5453061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453061 prefixEnd_5453061 := by exact prefixLift 5453061
  have htrace : WordTrace (prefixWord ++ tailWord_5453061) baseStart_5453061 baseEnd_5453061 := by
    simpa [prefixWord, tailWord_5453061, baseEnd_5453061] using wordTrace_append hprefix tailTrace_5453061
  have hstable : (prefixWord ++ tailWord_5453061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453061).length < 2 ^ (prefixWord ++ tailWord_5453061).sum := by decide
  have hdescent : baseEnd_5453061 < baseStart_5453061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453064 : List Nat := [2, 1, 3, 2, 4, 1, 1, 9]
def baseStart_5453064 : Nat := 118140960795 + 5453064 * 2 ^ 59
def prefixEnd_5453064 : Nat := 4983230072969 + 3 ^ 40 * 5453064 * 2
def baseEnd_5453064 : Nat := 103705291545524373915623

theorem tailTrace_5453064 : CollatzResearch.WordTrace tailWord_5453064 prefixEnd_5453064 103705291545524373915623 := by
  unfold tailWord_5453064
  simp only [CollatzResearch.WordTrace]
  refine ⟨99444791758243956015499123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132593055677658608020665497 99444791758243956015499123)
  ·
    refine ⟨149167187637365934023248685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99444791758243956015499123 149167187637365934023248685)
    ·
      refine ⟨55937695364012225258718257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149167187637365934023248685 55937695364012225258718257)
      ·
        refine ⟨41953271523009168944038693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55937695364012225258718257 41953271523009168944038693)
        ·
          refine ⟨7866238410564219177007255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41953271523009168944038693 7866238410564219177007255)
          ·
            refine ⟨11799357615846328765510883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7866238410564219177007255 11799357615846328765510883)
            ·
              refine ⟨17699036423769493148266325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11799357615846328765510883 17699036423769493148266325)
              ·
                refine ⟨103705291545524373915623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17699036423769493148266325 103705291545524373915623)
                ·
                  rfl

theorem cell23_5453064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 9].length) (baseStart_5453064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453064 prefixEnd_5453064 := by exact prefixLift 5453064
  have htrace : WordTrace (prefixWord ++ tailWord_5453064) baseStart_5453064 baseEnd_5453064 := by
    simpa [prefixWord, tailWord_5453064, baseEnd_5453064] using wordTrace_append hprefix tailTrace_5453064
  have hstable : (prefixWord ++ tailWord_5453064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453064).length < 2 ^ (prefixWord ++ tailWord_5453064).sum := by decide
  have hdescent : baseEnd_5453064 < baseStart_5453064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453077 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_5453077 : Nat := 118140960795 + 5453077 * 2 ^ 59
def prefixEnd_5453077 : Nat := 4983230072969 + 3 ^ 40 * 5453077 * 2
def baseEnd_5453077 : Nat := 933349848992555514953087

theorem tailTrace_5453077 : CollatzResearch.WordTrace tailWord_5453077 prefixEnd_5453077 933349848992555514953087 := by
  unfold tailWord_5453077
  simp only [CollatzResearch.WordTrace]
  refine ⟨198890057665440815251221485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132593371776960543500814323 198890057665440815251221485)
  ·
    refine ⟨74583771624540305719208057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198890057665440815251221485 74583771624540305719208057)
    ·
      refine ⟨55937828718405229289406043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74583771624540305719208057 55937828718405229289406043)
      ·
        refine ⟨83906743077607843934109065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55937828718405229289406043 83906743077607843934109065)
        ·
          refine ⟨62930057308205882950581799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83906743077607843934109065 62930057308205882950581799)
          ·
            refine ⟨94395085962308824425872699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62930057308205882950581799 94395085962308824425872699)
            ·
              refine ⟨141592628943463236638809049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94395085962308824425872699 141592628943463236638809049)
              ·
                refine ⟨106194471707597427479106787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141592628943463236638809049 106194471707597427479106787)
                ·
                  refine ⟨159291707561396141218660181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106194471707597427479106787 159291707561396141218660181)
                  ·
                    refine ⟨933349848992555514953087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 159291707561396141218660181 933349848992555514953087)
                    ·
                      rfl

theorem cell23_5453077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_5453077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453077 prefixEnd_5453077 := by exact prefixLift 5453077
  have htrace : WordTrace (prefixWord ++ tailWord_5453077) baseStart_5453077 baseEnd_5453077 := by
    simpa [prefixWord, tailWord_5453077, baseEnd_5453077] using wordTrace_append hprefix tailTrace_5453077
  have hstable : (prefixWord ++ tailWord_5453077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453077).length < 2 ^ (prefixWord ++ tailWord_5453077).sum := by decide
  have hdescent : baseEnd_5453077 < baseStart_5453077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453091 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 3]
def baseStart_5453091 : Nat := 118140960795 + 5453091 * 2 ^ 59
def prefixEnd_5453091 : Nat := 4983230072969 + 3 ^ 40 * 5453091 * 2
def baseEnd_5453091 : Nat := 2800056735706829490084197

theorem tailTrace_5453091 : CollatzResearch.WordTrace tailWord_5453091 prefixEnd_5453091 2800056735706829490084197 := by
  unfold tailWord_5453091
  simp only [CollatzResearch.WordTrace]
  refine ⟨198890568287390095642231127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132593712191593397094820751 198890568287390095642231127)
  ·
    refine ⟨298335852431085143463346691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198890568287390095642231127 298335852431085143463346691)
    ·
      refine ⟨447503778646627715195020037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298335852431085143463346691 447503778646627715195020037)
      ·
        refine ⟨83906958496242696599066257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 447503778646627715195020037 83906958496242696599066257)
        ·
          refine ⟨62930218872182022449299693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83906958496242696599066257 62930218872182022449299693)
          ·
            refine ⟨23598832077068258418487385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62930218872182022449299693 23598832077068258418487385)
            ·
              refine ⟨17699124057801193813865539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23598832077068258418487385 17699124057801193813865539)
              ·
                refine ⟨26548686086701790720798309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17699124057801193813865539 26548686086701790720798309)
                ·
                  refine ⟨4977878641256585760149683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26548686086701790720798309 4977878641256585760149683)
                  ·
                    refine ⟨7466817961884878640224525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4977878641256585760149683 7466817961884878640224525)
                    ·
                      refine ⟨2800056735706829490084197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7466817961884878640224525 2800056735706829490084197)
                      ·
                        rfl

theorem cell23_5453091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_5453091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453091 prefixEnd_5453091 := by exact prefixLift 5453091
  have htrace : WordTrace (prefixWord ++ tailWord_5453091) baseStart_5453091 baseEnd_5453091 := by
    simpa [prefixWord, tailWord_5453091, baseEnd_5453091] using wordTrace_append hprefix tailTrace_5453091
  have hstable : (prefixWord ++ tailWord_5453091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453091).length < 2 ^ (prefixWord ++ tailWord_5453091).sum := by decide
  have hdescent : baseEnd_5453091 < baseStart_5453091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453092 : List Nat := [2, 3, 1, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_5453092 : Nat := 118140960795 + 5453092 * 2 ^ 59
def prefixEnd_5453092 : Nat := 4983230072969 + 3 ^ 40 * 5453092 * 2
def baseEnd_5453092 : Nat := 2800057249187483986171693

theorem tailTrace_5453092 : CollatzResearch.WordTrace tailWord_5453092 prefixEnd_5453092 2800057249187483986171693 := by
  unfold tailWord_5453092
  simp only [CollatzResearch.WordTrace]
  refine ⟨99445302380193236406508765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132593736506924315208678353 99445302380193236406508765)
  ·
    refine ⟨37291988392572463652440787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99445302380193236406508765 37291988392572463652440787)
    ·
      refine ⟨55937982588858695478661181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37291988392572463652440787 55937982588858695478661181)
      ·
        refine ⟨20976743470822010804497943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55937982588858695478661181 20976743470822010804497943)
        ·
          refine ⟨31465115206233016206746915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20976743470822010804497943 31465115206233016206746915)
          ·
            refine ⟨47197672809349524310120373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31465115206233016206746915 47197672809349524310120373)
            ·
              refine ⟨4424781825876517904073785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47197672809349524310120373 4424781825876517904073785)
              ·
                refine ⟨3318586369407388428055339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424781825876517904073785 3318586369407388428055339)
                ·
                  refine ⟨4977879554111082642083009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318586369407388428055339 4977879554111082642083009)
                  ·
                    refine ⟨3733409665583311981562257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4977879554111082642083009 3733409665583311981562257)
                    ·
                      refine ⟨2800057249187483986171693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733409665583311981562257 2800057249187483986171693)
                      ·
                        rfl

theorem cell23_5453092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_5453092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453092 prefixEnd_5453092 := by exact prefixLift 5453092
  have htrace : WordTrace (prefixWord ++ tailWord_5453092) baseStart_5453092 baseEnd_5453092 := by
    simpa [prefixWord, tailWord_5453092, baseEnd_5453092] using wordTrace_append hprefix tailTrace_5453092
  have hstable : (prefixWord ++ tailWord_5453092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453092).length < 2 ^ (prefixWord ++ tailWord_5453092).sum := by decide
  have hdescent : baseEnd_5453092 < baseStart_5453092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453118 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_5453118 : Nat := 118140960795 + 5453118 * 2 ^ 59
def prefixEnd_5453118 : Nat := 4983230072969 + 3 ^ 40 * 5453118 * 2
def baseEnd_5453118 : Nat := 2800070599684500884446573

theorem tailTrace_5453118 : CollatzResearch.WordTrace tailWord_5453118 prefixEnd_5453118 2800070599684500884446573 := by
  unfold tailWord_5453118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24861444132286534906683001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132594368705528186168976005 24861444132286534906683001)
  ·
    refine ⟨18646083099214901180012251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24861444132286534906683001 18646083099214901180012251)
    ·
      refine ⟨27969124648822351770018377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18646083099214901180012251 27969124648822351770018377)
      ·
        refine ⟨20976843486616763827513783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27969124648822351770018377 20976843486616763827513783)
        ·
          refine ⟨31465265229925145741270675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20976843486616763827513783 31465265229925145741270675)
          ·
            refine ⟨47197897844887718611906013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31465265229925145741270675 47197897844887718611906013)
            ·
              refine ⟨17699211691832894479464755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47197897844887718611906013 17699211691832894479464755)
              ·
                refine ⟨26548817537749341719197133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17699211691832894479464755 26548817537749341719197133)
                ·
                  refine ⟨9955806576656003144698925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26548817537749341719197133 9955806576656003144698925)
                  ·
                    refine ⟨3733427466246001179262097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9955806576656003144698925 3733427466246001179262097)
                    ·
                      refine ⟨2800070599684500884446573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733427466246001179262097 2800070599684500884446573)
                      ·
                        rfl

theorem cell23_5453118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_5453118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453118 prefixEnd_5453118 := by exact prefixLift 5453118
  have htrace : WordTrace (prefixWord ++ tailWord_5453118) baseStart_5453118 baseEnd_5453118 := by
    simpa [prefixWord, tailWord_5453118, baseEnd_5453118] using wordTrace_append hprefix tailTrace_5453118
  have hstable : (prefixWord ++ tailWord_5453118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453118).length < 2 ^ (prefixWord ++ tailWord_5453118).sum := by decide
  have hdescent : baseEnd_5453118 < baseStart_5453118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453134 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_5453134 : Nat := 118140960795 + 5453134 * 2 ^ 59
def prefixEnd_5453134 : Nat := 4983230072969 + 3 ^ 40 * 5453134 * 2
def baseEnd_5453134 : Nat := 2800078815374972821846499

theorem tailTrace_5453134 : CollatzResearch.WordTrace tailWord_5453134 prefixEnd_5453134 2800078815374972821846499 := by
  unfold tailWord_5453134
  simp only [CollatzResearch.WordTrace]
  refine ⟨24861517078279289248255807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132594757750822875990697637 24861517078279289248255807)
  ·
    refine ⟨37292275617418933872383711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24861517078279289248255807 37292275617418933872383711)
    ·
      refine ⟨55938413426128400808575567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37292275617418933872383711 55938413426128400808575567)
      ·
        refine ⟨83907620139192601212863351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55938413426128400808575567 83907620139192601212863351)
        ·
          refine ⟨125861430208788901819295027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83907620139192601212863351 125861430208788901819295027)
          ·
            refine ⟨188792145313183352728942541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125861430208788901819295027 188792145313183352728942541)
            ·
              refine ⟨70797054492443757273353453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188792145313183352728942541 70797054492443757273353453)
              ·
                refine ⟨26548895434666408977507545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70797054492443757273353453 26548895434666408977507545)
                ·
                  refine ⟨19911671575999806733130659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26548895434666408977507545 19911671575999806733130659)
                  ·
                    refine ⟨29867507363999710099695989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19911671575999806733130659 29867507363999710099695989)
                    ·
                      refine ⟨2800078815374972821846499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29867507363999710099695989 2800078815374972821846499)
                      ·
                        rfl

theorem cell23_5453134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_5453134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453134 prefixEnd_5453134 := by exact prefixLift 5453134
  have htrace : WordTrace (prefixWord ++ tailWord_5453134) baseStart_5453134 baseEnd_5453134 := by
    simpa [prefixWord, tailWord_5453134, baseEnd_5453134] using wordTrace_append hprefix tailTrace_5453134
  have hstable : (prefixWord ++ tailWord_5453134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453134).length < 2 ^ (prefixWord ++ tailWord_5453134).sum := by decide
  have hdescent : baseEnd_5453134 < baseStart_5453134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453144 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_5453144 : Nat := 118140960795 + 5453144 * 2 ^ 59
def prefixEnd_5453144 : Nat := 4983230072969 + 3 ^ 40 * 5453144 * 2
def baseEnd_5453144 : Nat := 2800083950181517782721453

theorem tailTrace_5453144 : CollatzResearch.WordTrace tailWord_5453144 prefixEnd_5453144 2800083950181517782721453 := by
  unfold tailWord_5453144
  simp only [CollatzResearch.WordTrace]
  refine ⟨99446250678099042846955243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132595000904132057129273657 99446250678099042846955243)
  ·
    refine ⟨149169376017148564270432865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99446250678099042846955243 149169376017148564270432865)
    ·
      refine ⟨111877032012861423202824649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149169376017148564270432865 111877032012861423202824649)
      ·
        refine ⟨83907774009646067402118487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111877032012861423202824649 83907774009646067402118487)
        ·
          refine ⟨125861661014469101103177731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83907774009646067402118487 125861661014469101103177731)
          ·
            refine ⟨188792491521703651654766597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125861661014469101103177731 188792491521703651654766597)
            ·
              refine ⟨35398592160319434685268737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188792491521703651654766597 35398592160319434685268737)
              ·
                refine ⟨26548944120239576013951553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35398592160319434685268737 26548944120239576013951553)
                ·
                  refine ⟨19911708090179682010463665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26548944120239576013951553 19911708090179682010463665)
                  ·
                    refine ⟨14933781067634761507847749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19911708090179682010463665 14933781067634761507847749)
                    ·
                      refine ⟨2800083950181517782721453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14933781067634761507847749 2800083950181517782721453)
                      ·
                        rfl

theorem cell23_5453144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_5453144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453144 prefixEnd_5453144 := by exact prefixLift 5453144
  have htrace : WordTrace (prefixWord ++ tailWord_5453144) baseStart_5453144 baseEnd_5453144 := by
    simpa [prefixWord, tailWord_5453144, baseEnd_5453144] using wordTrace_append hprefix tailTrace_5453144
  have hstable : (prefixWord ++ tailWord_5453144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453144).length < 2 ^ (prefixWord ++ tailWord_5453144).sum := by decide
  have hdescent : baseEnd_5453144 < baseStart_5453144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453165 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_5453165 : Nat := 118140960795 + 5453165 * 2 ^ 59
def prefixEnd_5453165 : Nat := 4983230072969 + 3 ^ 40 * 5453165 * 2
def baseEnd_5453165 : Nat := 2800094733275262200558857

theorem tailTrace_5453165 : CollatzResearch.WordTrace tailWord_5453165 prefixEnd_5453165 2800094733275262200558857 := by
  unfold tailWord_5453165
  simp only [CollatzResearch.WordTrace]
  refine ⟨198893267289122006280424949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132595511526081337520283299 198893267289122006280424949)
  ·
    refine ⟨18646243808355188088789839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198893267289122006280424949 18646243808355188088789839)
    ·
      refine ⟨27969365712532782133184759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18646243808355188088789839 27969365712532782133184759)
      ·
        refine ⟨41954048568799173199777139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27969365712532782133184759 41954048568799173199777139)
        ·
          refine ⟨62931072853198759799665709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41954048568799173199777139 62931072853198759799665709)
          ·
            refine ⟨23599152319949534924874641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62931072853198759799665709 23599152319949534924874641)
            ·
              refine ⟨17699364239962151193655981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23599152319949534924874641 17699364239962151193655981)
              ·
                refine ⟨6637261589985806697620993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17699364239962151193655981 6637261589985806697620993)
                ·
                  refine ⟨4977946192489355023215745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6637261589985806697620993 4977946192489355023215745)
                  ·
                    refine ⟨3733459644367016267411809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4977946192489355023215745 3733459644367016267411809)
                    ·
                      refine ⟨2800094733275262200558857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733459644367016267411809 2800094733275262200558857)
                      ·
                        rfl

theorem cell23_5453165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_5453165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453165 prefixEnd_5453165 := by exact prefixLift 5453165
  have htrace : WordTrace (prefixWord ++ tailWord_5453165) baseStart_5453165 baseEnd_5453165 := by
    simpa [prefixWord, tailWord_5453165, baseEnd_5453165] using wordTrace_append hprefix tailTrace_5453165
  have hstable : (prefixWord ++ tailWord_5453165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453165).length < 2 ^ (prefixWord ++ tailWord_5453165).sum := by decide
  have hdescent : baseEnd_5453165 < baseStart_5453165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453188 : List Nat := [2, 3, 2, 1, 1, 4, 2, 3, 5]
def baseStart_5453188 : Nat := 118140960795 + 5453188 * 2 ^ 59
def prefixEnd_5453188 : Nat := 4983230072969 + 3 ^ 40 * 5453188 * 2
def baseEnd_5453188 : Nat := 311122949258923956730139

theorem tailTrace_5453188 : CollatzResearch.WordTrace tailWord_5453188 prefixEnd_5453188 311122949258923956730139 := by
  unfold tailWord_5453188
  simp only [CollatzResearch.WordTrace]
  refine ⟨99447053084019340604256109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132596070778692454139008145 99447053084019340604256109)
  ·
    refine ⟨37292644906507252726596041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99447053084019340604256109 37292644906507252726596041)
    ·
      refine ⟨27969483679880439544947031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37292644906507252726596041 27969483679880439544947031)
      ·
        refine ⟨41954225519820659317420547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27969483679880439544947031 41954225519820659317420547)
        ·
          refine ⟨62931338279730988976130821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41954225519820659317420547 62931338279730988976130821)
          ·
            refine ⟨11799625927449560433024529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62931338279730988976130821 11799625927449560433024529)
            ·
              refine ⟨8849719445587170324768397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11799625927449560433024529 8849719445587170324768397)
              ·
                refine ⟨3318644792095188871788149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8849719445587170324768397 3318644792095188871788149)
                ·
                  refine ⟨311122949258923956730139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3318644792095188871788149 311122949258923956730139)
                  ·
                    rfl

theorem cell23_5453188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_5453188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453188 prefixEnd_5453188 := by exact prefixLift 5453188
  have htrace : WordTrace (prefixWord ++ tailWord_5453188) baseStart_5453188 baseEnd_5453188 := by
    simpa [prefixWord, tailWord_5453188, baseEnd_5453188] using wordTrace_append hprefix tailTrace_5453188
  have hstable : (prefixWord ++ tailWord_5453188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453188).length < 2 ^ (prefixWord ++ tailWord_5453188).sum := by decide
  have hdescent : baseEnd_5453188 < baseStart_5453188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453221 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 1, 6, 2]
def baseStart_5453221 : Nat := 118140960795 + 5453221 * 2 ^ 59
def prefixEnd_5453221 : Nat := 4983230072969 + 3 ^ 40 * 5453221 * 2
def baseEnd_5453221 : Nat := 2800123488191913981458599

theorem tailTrace_5453221 : CollatzResearch.WordTrace tailWord_5453221 prefixEnd_5453221 2800123488191913981458599 := by
  unfold tailWord_5453221
  simp only [CollatzResearch.WordTrace]
  refine ⟨198895309776919127844463517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132596873184612751896309011 198895309776919127844463517)
  ·
    refine ⟨74585741166344672941673819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198895309776919127844463517 74585741166344672941673819)
    ·
      refine ⟨111878611749517009412510729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74585741166344672941673819 111878611749517009412510729)
      ·
        refine ⟨83908958812137757059383047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111878611749517009412510729 83908958812137757059383047)
        ·
          refine ⟨125863438218206635589074571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83908958812137757059383047 125863438218206635589074571)
          ·
            refine ⟨188795157327309953383611857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125863438218206635589074571 188795157327309953383611857)
            ·
              refine ⟨141596367995482465037708893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188795157327309953383611857 141596367995482465037708893)
              ·
                refine ⟨53098637998305924389140835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141596367995482465037708893 53098637998305924389140835)
                ·
                  refine ⟨79647956997458886583711253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53098637998305924389140835 79647956997458886583711253)
                  ·
                    refine ⟨3733497984255885308611465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79647956997458886583711253 3733497984255885308611465)
                    ·
                      refine ⟨2800123488191913981458599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733497984255885308611465 2800123488191913981458599)
                      ·
                        rfl

theorem cell23_5453221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_5453221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453221 prefixEnd_5453221 := by exact prefixLift 5453221
  have htrace : WordTrace (prefixWord ++ tailWord_5453221) baseStart_5453221 baseEnd_5453221 := by
    simpa [prefixWord, tailWord_5453221, baseEnd_5453221] using wordTrace_append hprefix tailTrace_5453221
  have hstable : (prefixWord ++ tailWord_5453221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453221).length < 2 ^ (prefixWord ++ tailWord_5453221).sum := by decide
  have hdescent : baseEnd_5453221 < baseStart_5453221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453234 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_5453234 : Nat := 118140960795 + 5453234 * 2 ^ 59
def prefixEnd_5453234 : Nat := 4983230072969 + 3 ^ 40 * 5453234 * 2
def baseEnd_5453234 : Nat := 2800130163440422430596039

theorem tailTrace_5453234 : CollatzResearch.WordTrace tailWord_5453234 prefixEnd_5453234 2800130163440422430596039 := by
  unfold tailWord_5453234
  simp only [CollatzResearch.WordTrace]
  refine ⟨49723945981468007766171689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132597189283914687376457837 49723945981468007766171689)
  ·
    refine ⟨37292959486101005824628767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49723945981468007766171689 37292959486101005824628767)
    ·
      refine ⟨55939439229151508736943151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37292959486101005824628767 55939439229151508736943151)
      ·
        refine ⟨83909158843727263105414727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55939439229151508736943151 83909158843727263105414727)
        ·
          refine ⟨125863738265590894658122091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83909158843727263105414727 125863738265590894658122091)
          ·
            refine ⟨188795607398386341987183137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125863738265590894658122091 188795607398386341987183137)
            ·
              refine ⟨141596705548789756490387353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188795607398386341987183137 141596705548789756490387353)
              ·
                refine ⟨106197529161592317367790515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141596705548789756490387353 106197529161592317367790515)
                ·
                  refine ⟨159296293742388476051685773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106197529161592317367790515 159296293742388476051685773)
                  ·
                    refine ⟨59736110153395678519382165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159296293742388476051685773 59736110153395678519382165)
                    ·
                      refine ⟨2800130163440422430596039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59736110153395678519382165 2800130163440422430596039)
                      ·
                        rfl

theorem cell23_5453234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_5453234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453234 prefixEnd_5453234 := by exact prefixLift 5453234
  have htrace : WordTrace (prefixWord ++ tailWord_5453234) baseStart_5453234 baseEnd_5453234 := by
    simpa [prefixWord, tailWord_5453234, baseEnd_5453234] using wordTrace_append hprefix tailTrace_5453234
  have hstable : (prefixWord ++ tailWord_5453234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453234).length < 2 ^ (prefixWord ++ tailWord_5453234).sum := by decide
  have hdescent : baseEnd_5453234 < baseStart_5453234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453258 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_5453258 : Nat := 118140960795 + 5453258 * 2 ^ 59
def prefixEnd_5453258 : Nat := 4983230072969 + 3 ^ 40 * 5453258 * 2
def baseEnd_5453258 : Nat := 2800142486976130336695929

theorem tailTrace_5453258 : CollatzResearch.WordTrace tailWord_5453258 prefixEnd_5453258 2800142486976130336695929 := by
  unfold tailWord_5453258
  simp only [CollatzResearch.WordTrace]
  refine ⟨49724164819446270790890107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132597772851856722109040285 49724164819446270790890107)
  ·
    refine ⟨74586247229169406186335161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49724164819446270790890107 74586247229169406186335161)
    ·
      refine ⟨55939685421877054639751371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74586247229169406186335161 55939685421877054639751371)
      ·
        refine ⟨83909528132815581959627057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55939685421877054639751371 83909528132815581959627057)
        ·
          refine ⟨62932146099611686469720293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83909528132815581959627057 62932146099611686469720293)
          ·
            refine ⟨11799777393677191213072555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62932146099611686469720293 11799777393677191213072555)
            ·
              refine ⟨17699666090515786819608833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11799777393677191213072555 17699666090515786819608833)
              ·
                refine ⟨13274749567886840114706625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17699666090515786819608833 13274749567886840114706625)
                ·
                  refine ⟨9956062175915130086029969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13274749567886840114706625 9956062175915130086029969)
                  ·
                    refine ⟨7467046631936347564522477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9956062175915130086029969 7467046631936347564522477)
                    ·
                      refine ⟨2800142486976130336695929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467046631936347564522477 2800142486976130336695929)
                      ·
                        rfl

theorem cell23_5453258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_5453258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453258 prefixEnd_5453258 := by exact prefixLift 5453258
  have htrace : WordTrace (prefixWord ++ tailWord_5453258) baseStart_5453258 baseEnd_5453258 := by
    simpa [prefixWord, tailWord_5453258, baseEnd_5453258] using wordTrace_append hprefix tailTrace_5453258
  have hstable : (prefixWord ++ tailWord_5453258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453258).length < 2 ^ (prefixWord ++ tailWord_5453258).sum := by decide
  have hdescent : baseEnd_5453258 < baseStart_5453258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453288 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_5453288 : Nat := 118140960795 + 5453288 * 2 ^ 59
def prefixEnd_5453288 : Nat := 4983230072969 + 3 ^ 40 * 5453288 * 2
def baseEnd_5453288 : Nat := 2800157891395765219320791

theorem tailTrace_5453288 : CollatzResearch.WordTrace tailWord_5453288 prefixEnd_5453288 2800157891395765219320791 := by
  unfold tailWord_5453288
  simp only [CollatzResearch.WordTrace]
  refine ⟨99448876733838199143576259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132598502311784265524768345 99448876733838199143576259)
  ·
    refine ⟨149173315100757298715364389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99448876733838199143576259 149173315100757298715364389)
    ·
      refine ⟨27969996581391993509130823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149173315100757298715364389 27969996581391993509130823)
      ·
        refine ⟨41954994872087990263696235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27969996581391993509130823 41954994872087990263696235)
        ·
          refine ⟨62932492308131985395544353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41954994872087990263696235 62932492308131985395544353)
          ·
            refine ⟨47199369231098989046658265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62932492308131985395544353 47199369231098989046658265)
            ·
              refine ⟨35399526923324241784993699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47199369231098989046658265 35399526923324241784993699)
              ·
                refine ⟨53099290384986362677490549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35399526923324241784993699 53099290384986362677490549)
                ·
                  refine ⟨4978058473592471501014739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53099290384986362677490549 4978058473592471501014739)
                  ·
                    refine ⟨7467087710388707251522109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4978058473592471501014739 7467087710388707251522109)
                    ·
                      refine ⟨2800157891395765219320791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467087710388707251522109 2800157891395765219320791)
                      ·
                        rfl

theorem cell23_5453288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_5453288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453288 prefixEnd_5453288 := by exact prefixLift 5453288
  have htrace : WordTrace (prefixWord ++ tailWord_5453288) baseStart_5453288 baseEnd_5453288 := by
    simpa [prefixWord, tailWord_5453288, baseEnd_5453288] using wordTrace_append hprefix tailTrace_5453288
  have hstable : (prefixWord ++ tailWord_5453288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453288).length < 2 ^ (prefixWord ++ tailWord_5453288).sum := by decide
  have hdescent : baseEnd_5453288 < baseStart_5453288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453291 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 1, 5]
def baseStart_5453291 : Nat := 118140960795 + 5453291 * 2 ^ 59
def prefixEnd_5453291 : Nat := 4983230072969 + 3 ^ 40 * 5453291 * 2
def baseEnd_5453291 : Nat := 933386477279242902527759

theorem tailTrace_5453291 : CollatzResearch.WordTrace tailWord_5453291 prefixEnd_5453291 933386477279242902527759 := by
  unfold tailWord_5453291
  simp only [CollatzResearch.WordTrace]
  refine ⟨198897862886665529799511727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132598575257777019866341151 198897862886665529799511727)
  ·
    refine ⟨298346794329998294699267591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198897862886665529799511727 298346794329998294699267591)
    ·
      refine ⟨447520191494997442048901387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298346794329998294699267591 447520191494997442048901387)
      ·
        refine ⟨671280287242496163073352081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447520191494997442048901387 671280287242496163073352081)
        ·
          refine ⟨503460215431872122305014061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671280287242496163073352081 503460215431872122305014061)
          ·
            refine ⟨188797580786952045864380273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 503460215431872122305014061 188797580786952045864380273)
            ·
              refine ⟨141598185590214034398285205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188797580786952045864380273 141598185590214034398285205)
              ·
                refine ⟨6637414949541282862419619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141598185590214034398285205 6637414949541282862419619)
                ·
                  refine ⟨9956122424311924293629429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6637414949541282862419619 9956122424311924293629429)
                  ·
                    refine ⟨933386477279242902527759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9956122424311924293629429 933386477279242902527759)
                    ·
                      rfl

theorem cell23_5453291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 5].length) (baseStart_5453291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453291 prefixEnd_5453291 := by exact prefixLift 5453291
  have htrace : WordTrace (prefixWord ++ tailWord_5453291) baseStart_5453291 baseEnd_5453291 := by
    simpa [prefixWord, tailWord_5453291, baseEnd_5453291] using wordTrace_append hprefix tailTrace_5453291
  have hstable : (prefixWord ++ tailWord_5453291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453291).length < 2 ^ (prefixWord ++ tailWord_5453291).sum := by decide
  have hdescent : baseEnd_5453291 < baseStart_5453291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453305 : List Nat := [1, 2, 1, 3, 1, 2, 1, 7, 1, 1, 3]
def baseStart_5453305 : Nat := 118140960795 + 5453305 * 2 ^ 59
def prefixEnd_5453305 : Nat := 4983230072969 + 3 ^ 40 * 5453305 * 2
def baseEnd_5453305 : Nat := 2800166620566891652808213

theorem tailTrace_5453305 : CollatzResearch.WordTrace tailWord_5453305 prefixEnd_5453305 2800166620566891652808213 := by
  unfold tailWord_5453305
  simp only [CollatzResearch.WordTrace]
  refine ⟨198898373508614810190521369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132598915672409873460347579 198898373508614810190521369)
  ·
    refine ⟨149173780131461107642891027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198898373508614810190521369 149173780131461107642891027)
    ·
      refine ⟨223760670197191661464336541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149173780131461107642891027 223760670197191661464336541)
      ·
        refine ⟨83910251323946873049126203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223760670197191661464336541 83910251323946873049126203)
        ·
          refine ⟨125865376985920309573689305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83910251323946873049126203 125865376985920309573689305)
          ·
            refine ⟨94399032739440232180266979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125865376985920309573689305 94399032739440232180266979)
            ·
              refine ⟨141598549109160348270400469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94399032739440232180266979 141598549109160348270400469)
              ·
                refine ⟨3318715994745945662587511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 141598549109160348270400469 3318715994745945662587511)
                ·
                  refine ⟨4978073992118918493881267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318715994745945662587511 4978073992118918493881267)
                  ·
                    refine ⟨7467110988178377740821901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4978073992118918493881267 7467110988178377740821901)
                    ·
                      refine ⟨2800166620566891652808213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467110988178377740821901 2800166620566891652808213)
                      ·
                        rfl

theorem cell23_5453305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_5453305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453305 prefixEnd_5453305 := by exact prefixLift 5453305
  have htrace : WordTrace (prefixWord ++ tailWord_5453305) baseStart_5453305 baseEnd_5453305 := by
    simpa [prefixWord, tailWord_5453305, baseEnd_5453305] using wordTrace_append hprefix tailTrace_5453305
  have hstable : (prefixWord ++ tailWord_5453305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453305).length < 2 ^ (prefixWord ++ tailWord_5453305).sum := by decide
  have hdescent : baseEnd_5453305 < baseStart_5453305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453316 : List Nat := [2, 3, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_5453316 : Nat := 118140960795 + 5453316 * 2 ^ 59
def prefixEnd_5453316 : Nat := 4983230072969 + 3 ^ 40 * 5453316 * 2
def baseEnd_5453316 : Nat := 933390756284697036590221

theorem tailTrace_5453316 : CollatzResearch.WordTrace tailWord_5453316 prefixEnd_5453316 933390756284697036590221 := by
  unfold tailWord_5453316
  simp only [CollatzResearch.WordTrace]
  refine ⟨99449387355787479534585901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132599183141049972712781201 99449387355787479534585901)
  ·
    refine ⟨37293520258420304825469713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99449387355787479534585901 37293520258420304825469713)
    ·
      refine ⟨27970140193815228619102285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37293520258420304825469713 27970140193815228619102285)
      ·
        refine ⟨10488802572680710732163357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27970140193815228619102285 10488802572680710732163357)
        ·
          refine ⟨3933300964755266524561259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10488802572680710732163357 3933300964755266524561259)
          ·
            refine ⟨5899951447132899786841889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933300964755266524561259 5899951447132899786841889)
            ·
              refine ⟨4424963585349674840131417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5899951447132899786841889 4424963585349674840131417)
              ·
                refine ⟨3318722689012256130098563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424963585349674840131417 3318722689012256130098563)
                ·
                  refine ⟨4978084033518384195147845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318722689012256130098563 4978084033518384195147845)
                  ·
                    refine ⟨933390756284697036590221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4978084033518384195147845 933390756284697036590221)
                    ·
                      rfl

theorem cell23_5453316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_5453316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453316 prefixEnd_5453316 := by exact prefixLift 5453316
  have htrace : WordTrace (prefixWord ++ tailWord_5453316) baseStart_5453316 baseEnd_5453316 := by
    simpa [prefixWord, tailWord_5453316, baseEnd_5453316] using wordTrace_append hprefix tailTrace_5453316
  have hstable : (prefixWord ++ tailWord_5453316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453316).length < 2 ^ (prefixWord ++ tailWord_5453316).sum := by decide
  have hdescent : baseEnd_5453316 < baseStart_5453316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453322 : List Nat := [3, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_5453322 : Nat := 118140960795 + 5453322 * 2 ^ 59
def prefixEnd_5453322 : Nat := 4983230072969 + 3 ^ 40 * 5453322 * 2
def baseEnd_5453322 : Nat := 2800175349738018086295635

theorem tailTrace_5453322 : CollatzResearch.WordTrace tailWord_5453322 prefixEnd_5453322 2800175349738018086295635 := by
  unfold tailWord_5453322
  simp only [CollatzResearch.WordTrace]
  refine ⟨49724748387388305523472555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132599329033035481395926813 49724748387388305523472555)
  ·
    refine ⟨74587122581082458285208833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49724748387388305523472555 74587122581082458285208833)
    ·
      refine ⟨55940341935811843713906625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74587122581082458285208833 55940341935811843713906625)
      ·
        refine ⟨41955256451858882785429969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55940341935811843713906625 41955256451858882785429969)
        ·
          refine ⟨31466442338894162089072477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41955256451858882785429969 31466442338894162089072477)
          ·
            refine ⟨11799915877085310783402179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31466442338894162089072477 11799915877085310783402179)
            ·
              refine ⟨17699873815627966175103269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11799915877085310783402179 17699873815627966175103269)
              ·
                refine ⟨3318726340430243657831863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17699873815627966175103269 3318726340430243657831863)
                ·
                  refine ⟨4978089510645365486747795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318726340430243657831863 4978089510645365486747795)
                  ·
                    refine ⟨7467134265968048230121693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4978089510645365486747795 7467134265968048230121693)
                    ·
                      refine ⟨2800175349738018086295635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467134265968048230121693 2800175349738018086295635)
                      ·
                        rfl

theorem cell23_5453322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_5453322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453322 prefixEnd_5453322 := by exact prefixLift 5453322
  have htrace : WordTrace (prefixWord ++ tailWord_5453322) baseStart_5453322 baseEnd_5453322 := by
    simpa [prefixWord, tailWord_5453322, baseEnd_5453322] using wordTrace_append hprefix tailTrace_5453322
  have hstable : (prefixWord ++ tailWord_5453322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453322).length < 2 ^ (prefixWord ++ tailWord_5453322).sum := by decide
  have hdescent : baseEnd_5453322 < baseStart_5453322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453345 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_5453345 : Nat := 118140960795 + 5453345 * 2 ^ 59
def prefixEnd_5453345 : Nat := 4983230072969 + 3 ^ 40 * 5453345 * 2
def baseEnd_5453345 : Nat := 2800187159793071496308029

theorem tailTrace_5453345 : CollatzResearch.WordTrace tailWord_5453345 prefixEnd_5453345 2800187159793071496308029 := by
  unfold tailWord_5453345
  simp only [CollatzResearch.WordTrace]
  refine ⟨198899832428469897021977489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132599888285646598014651659 198899832428469897021977489)
  ·
    refine ⟨149174874321352422766483117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198899832428469897021977489 149174874321352422766483117)
    ·
      refine ⟨55940577870507158537431169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149174874321352422766483117 55940577870507158537431169)
      ·
        refine ⟨41955433402880368903073377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55940577870507158537431169 41955433402880368903073377)
        ·
          refine ⟨31466575052160276677305033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41955433402880368903073377 31466575052160276677305033)
          ·
            refine ⟨23599931289120207507978775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31466575052160276677305033 23599931289120207507978775)
            ·
              refine ⟨35399896933680311261968163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23599931289120207507978775 35399896933680311261968163)
              ·
                refine ⟨53099845400520466892952245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35399896933680311261968163 53099845400520466892952245)
                ·
                  refine ⟨4978110506298793771214273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53099845400520466892952245 4978110506298793771214273)
                  ·
                    refine ⟨3733582879724095328410705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4978110506298793771214273 3733582879724095328410705)
                    ·
                      refine ⟨2800187159793071496308029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733582879724095328410705 2800187159793071496308029)
                      ·
                        rfl

theorem cell23_5453345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_5453345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453345 prefixEnd_5453345 := by exact prefixLift 5453345
  have htrace : WordTrace (prefixWord ++ tailWord_5453345) baseStart_5453345 baseEnd_5453345 := by
    simpa [prefixWord, tailWord_5453345, baseEnd_5453345] using wordTrace_append hprefix tailTrace_5453345
  have hstable : (prefixWord ++ tailWord_5453345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453345).length < 2 ^ (prefixWord ++ tailWord_5453345).sum := by decide
  have hdescent : baseEnd_5453345 < baseStart_5453345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453365 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_5453365 : Nat := 118140960795 + 5453365 * 2 ^ 59
def prefixEnd_5453365 : Nat := 4983230072969 + 3 ^ 40 * 5453365 * 2
def baseEnd_5453365 : Nat := 2800197429406161418057937

theorem tailTrace_5453365 : CollatzResearch.WordTrace tailWord_5453365 prefixEnd_5453365 2800197429406161418057937 := by
  unfold tailWord_5453365
  simp only [CollatzResearch.WordTrace]
  refine ⟨198900561888397440437705549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132600374592264960291803699 198900561888397440437705549)
  ·
    refine ⟨74587710708149040164139581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198900561888397440437705549 74587710708149040164139581)
    ·
      refine ⟨27970391515555890061552343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74587710708149040164139581 27970391515555890061552343)
      ·
        refine ⟨41955587273333835092328515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27970391515555890061552343 41955587273333835092328515)
        ·
          refine ⟨62933380910000752638492773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41955587273333835092328515 62933380910000752638492773)
          ·
            refine ⟨11800008920625141119717395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62933380910000752638492773 11800008920625141119717395)
            ·
              refine ⟨17700013380937711679576093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11800008920625141119717395 17700013380937711679576093)
              ·
                refine ⟨6637505017851641879841035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17700013380937711679576093 6637505017851641879841035)
                ·
                  refine ⟨9956257526777462819761553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6637505017851641879841035 9956257526777462819761553)
                  ·
                    refine ⟨7467193145083097114821165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9956257526777462819761553 7467193145083097114821165)
                    ·
                      refine ⟨2800197429406161418057937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467193145083097114821165 2800197429406161418057937)
                      ·
                        rfl

theorem cell23_5453365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_5453365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453365 prefixEnd_5453365 := by exact prefixLift 5453365
  have htrace : WordTrace (prefixWord ++ tailWord_5453365) baseStart_5453365 baseEnd_5453365 := by
    simpa [prefixWord, tailWord_5453365, baseEnd_5453365] using wordTrace_append hprefix tailTrace_5453365
  have hstable : (prefixWord ++ tailWord_5453365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453365).length < 2 ^ (prefixWord ++ tailWord_5453365).sum := by decide
  have hdescent : baseEnd_5453365 < baseStart_5453365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453372 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_5453372 : Nat := 118140960795 + 5453372 * 2 ^ 59
def prefixEnd_5453372 : Nat := 4983230072969 + 3 ^ 40 * 5453372 * 2
def baseEnd_5453372 : Nat := 933400341256914296890135

theorem tailTrace_5453372 : CollatzResearch.WordTrace tailWord_5453372 prefixEnd_5453372 933400341256914296890135 := by
  unfold tailWord_5453372
  simp only [CollatzResearch.WordTrace]
  refine ⟨99450408599686040316605185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132600544799581387088806913 99450408599686040316605185)
  ·
    refine ⟨74587806449764530237453889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99450408599686040316605185 74587806449764530237453889)
    ·
      refine ⟨55940854837323397678090417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74587806449764530237453889 55940854837323397678090417)
      ·
        refine ⟨41955641127992548258567813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55940854837323397678090417 41955641127992548258567813)
        ·
          refine ⟨7866682711498602798481465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41955641127992548258567813 7866682711498602798481465)
          ·
            refine ⟨5900012033623952098861099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7866682711498602798481465 5900012033623952098861099)
            ·
              refine ⟨8850018050435928148291649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900012033623952098861099 8850018050435928148291649)
              ·
                refine ⟨6637513537826946111218737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8850018050435928148291649 6637513537826946111218737)
                ·
                  refine ⟨4978135153370209583414053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6637513537826946111218737 4978135153370209583414053)
                  ·
                    refine ⟨933400341256914296890135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4978135153370209583414053 933400341256914296890135)
                    ·
                      rfl

theorem cell23_5453372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_5453372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453372 prefixEnd_5453372 := by exact prefixLift 5453372
  have htrace : WordTrace (prefixWord ++ tailWord_5453372) baseStart_5453372 baseEnd_5453372 := by
    simpa [prefixWord, tailWord_5453372, baseEnd_5453372] using wordTrace_append hprefix tailTrace_5453372
  have hstable : (prefixWord ++ tailWord_5453372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453372).length < 2 ^ (prefixWord ++ tailWord_5453372).sum := by decide
  have hdescent : baseEnd_5453372 < baseStart_5453372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453382 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_5453382 : Nat := 118140960795 + 5453382 * 2 ^ 59
def prefixEnd_5453382 : Nat := 4983230072969 + 3 ^ 40 * 5453382 * 2
def baseEnd_5453382 : Nat := 2800206158577287851545359

theorem tailTrace_5453382 : CollatzResearch.WordTrace tailWord_5453382 prefixEnd_5453382 2800206158577287851545359 := by
  unfold tailWord_5453382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215661935291745385658575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132600787952890568227382933 6215661935291745385658575)
  ·
    refine ⟨9323492902937618078487863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6215661935291745385658575 9323492902937618078487863)
    ·
      refine ⟨13985239354406427117731795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9323492902937618078487863 13985239354406427117731795)
      ·
        refine ⟨20977859031609640676597693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13985239354406427117731795 20977859031609640676597693)
        ·
          refine ⟨7866697136853615253724135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20977859031609640676597693 7866697136853615253724135)
          ·
            refine ⟨11800045705280422880586203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7866697136853615253724135 11800045705280422880586203)
            ·
              refine ⟨17700068557920634320879305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11800045705280422880586203 17700068557920634320879305)
              ·
                refine ⟨13275051418440475740659479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17700068557920634320879305 13275051418440475740659479)
                ·
                  refine ⟨19912577127660713610989219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13275051418440475740659479 19912577127660713610989219)
                  ·
                    refine ⟨29868865691491070416483829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19912577127660713610989219 29868865691491070416483829)
                    ·
                      refine ⟨2800206158577287851545359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29868865691491070416483829 2800206158577287851545359)
                      ·
                        rfl

theorem cell23_5453382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_5453382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453382 prefixEnd_5453382 := by exact prefixLift 5453382
  have htrace : WordTrace (prefixWord ++ tailWord_5453382) baseStart_5453382 baseEnd_5453382 := by
    simpa [prefixWord, tailWord_5453382, baseEnd_5453382] using wordTrace_append hprefix tailTrace_5453382
  have hstable : (prefixWord ++ tailWord_5453382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453382).length < 2 ^ (prefixWord ++ tailWord_5453382).sum := by decide
  have hdescent : baseEnd_5453382 < baseStart_5453382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453389 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_5453389 : Nat := 118140960795 + 5453389 * 2 ^ 59
def prefixEnd_5453389 : Nat := 4983230072969 + 3 ^ 40 * 5453389 * 2
def baseEnd_5453389 : Nat := 933403250980623108052609

theorem tailTrace_5453389 : CollatzResearch.WordTrace tailWord_5453389 prefixEnd_5453389 933403250980623108052609 := by
  unfold tailWord_5453389
  simp only [CollatzResearch.WordTrace]
  refine ⟨198901437240310492536579221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132600958160206995024386147 198901437240310492536579221)
  ·
    refine ⟨9323504870639554337652151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198901437240310492536579221 9323504870639554337652151)
    ·
      refine ⟨13985257305959331506478227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9323504870639554337652151 13985257305959331506478227)
      ·
        refine ⟨20977885958938997259717341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13985257305959331506478227 20977885958938997259717341)
        ·
          refine ⟨7866707234602123972394003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20977885958938997259717341 7866707234602123972394003)
          ·
            refine ⟨11800060851903185958591005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7866707234602123972394003 11800060851903185958591005)
            ·
              refine ⟨4425022819463694734471627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11800060851903185958591005 4425022819463694734471627)
              ·
                refine ⟨6637534229195542101707441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425022819463694734471627 6637534229195542101707441)
                ·
                  refine ⟨4978150671896656576280581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6637534229195542101707441 4978150671896656576280581)
                  ·
                    refine ⟨933403250980623108052609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4978150671896656576280581 933403250980623108052609)
                    ·
                      rfl

theorem cell23_5453389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_5453389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453389 prefixEnd_5453389 := by exact prefixLift 5453389
  have htrace : WordTrace (prefixWord ++ tailWord_5453389) baseStart_5453389 baseEnd_5453389 := by
    simpa [prefixWord, tailWord_5453389, baseEnd_5453389] using wordTrace_append hprefix tailTrace_5453389
  have hstable : (prefixWord ++ tailWord_5453389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453389).length < 2 ^ (prefixWord ++ tailWord_5453389).sum := by decide
  have hdescent : baseEnd_5453389 < baseStart_5453389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453401 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_5453401 : Nat := 118140960795 + 5453401 * 2 ^ 59
def prefixEnd_5453401 : Nat := 4983230072969 + 3 ^ 40 * 5453401 * 2
def baseEnd_5453401 : Nat := 2800215914709723277207771

theorem tailTrace_5453401 : CollatzResearch.WordTrace tailWord_5453401 prefixEnd_5453401 2800215914709723277207771 := by
  unfold tailWord_5453401
  simp only [CollatzResearch.WordTrace]
  refine ⟨198901874916267018586016057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132601249944178012390677371 198901874916267018586016057)
  ·
    refine ⟨149176406187200263939512043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198901874916267018586016057 149176406187200263939512043)
    ·
      refine ⟨223764609280800395909268065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149176406187200263939512043 223764609280800395909268065)
      ·
        refine ⟨167823456960600296931951049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223764609280800395909268065 167823456960600296931951049)
        ·
          refine ⟨125867592720450222698963287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167823456960600296931951049 125867592720450222698963287)
          ·
            refine ⟨188801389080675334048444931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125867592720450222698963287 188801389080675334048444931)
            ·
              refine ⟨283202083621013001072667397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188801389080675334048444931 283202083621013001072667397)
              ·
                refine ⟨53100390678939937701125137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283202083621013001072667397 53100390678939937701125137)
                ·
                  refine ⟨39825293009204953275843853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53100390678939937701125137 39825293009204953275843853)
                  ·
                    refine ⟨14934484878451857478441445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39825293009204953275843853 14934484878451857478441445)
                    ·
                      refine ⟨2800215914709723277207771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14934484878451857478441445 2800215914709723277207771)
                      ·
                        rfl

theorem cell23_5453401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_5453401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453401 prefixEnd_5453401 := by exact prefixLift 5453401
  have htrace : WordTrace (prefixWord ++ tailWord_5453401) baseStart_5453401 baseEnd_5453401 := by
    simpa [prefixWord, tailWord_5453401, baseEnd_5453401] using wordTrace_append hprefix tailTrace_5453401
  have hstable : (prefixWord ++ tailWord_5453401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453401).length < 2 ^ (prefixWord ++ tailWord_5453401).sum := by decide
  have hdescent : baseEnd_5453401 < baseStart_5453401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453435 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 4, 2, 2]
def baseStart_5453435 : Nat := 118140960795 + 5453435 * 2 ^ 59
def prefixEnd_5453435 : Nat := 4983230072969 + 3 ^ 40 * 5453435 * 2
def baseEnd_5453435 : Nat := 2800233373051976144182615

theorem tailTrace_5453435 : CollatzResearch.WordTrace tailWord_5453435 prefixEnd_5453435 2800233373051976144182615 := by
  unfold tailWord_5453435
  simp only [CollatzResearch.WordTrace]
  refine ⟨198903114998143842392753759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132602076665429228261835839 198903114998143842392753759)
  ·
    refine ⟨298354672497215763589130639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198903114998143842392753759 298354672497215763589130639)
    ·
      refine ⟨447532008745823645383695959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298354672497215763589130639 447532008745823645383695959)
      ·
        refine ⟨671298013118735468075543939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447532008745823645383695959 671298013118735468075543939)
        ·
          refine ⟨1006947019678103202113315909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671298013118735468075543939 1006947019678103202113315909)
          ·
            refine ⟨188802566189644350396246733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1006947019678103202113315909 188802566189644350396246733)
            ·
              refine ⟨70800962321116631398592525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188802566189644350396246733 70800962321116631398592525)
              ·
                refine ⟨26550360870418736774472197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70800962321116631398592525 26550360870418736774472197)
                ·
                  refine ⟨4978192663203513145213537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26550360870418736774472197 4978192663203513145213537)
                  ·
                    refine ⟨3733644497402634858910153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4978192663203513145213537 3733644497402634858910153)
                    ·
                      refine ⟨2800233373051976144182615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733644497402634858910153 2800233373051976144182615)
                      ·
                        rfl

theorem cell23_5453435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 2, 2].length) (baseStart_5453435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453435 prefixEnd_5453435 := by exact prefixLift 5453435
  have htrace : WordTrace (prefixWord ++ tailWord_5453435) baseStart_5453435 baseEnd_5453435 := by
    simpa [prefixWord, tailWord_5453435, baseEnd_5453435] using wordTrace_append hprefix tailTrace_5453435
  have hstable : (prefixWord ++ tailWord_5453435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453435).length < 2 ^ (prefixWord ++ tailWord_5453435).sum := by decide
  have hdescent : baseEnd_5453435 < baseStart_5453435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453452 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 2, 2, 2]
def baseStart_5453452 : Nat := 118140960795 + 5453452 * 2 ^ 59
def prefixEnd_5453452 : Nat := 4983230072969 + 3 ^ 40 * 5453452 * 2
def baseEnd_5453452 : Nat := 2800242102223102577670037

theorem tailTrace_5453452 : CollatzResearch.WordTrace tailWord_5453452 prefixEnd_5453452 2800242102223102577670037 := by
  unfold tailWord_5453452
  simp only [CollatzResearch.WordTrace]
  refine ⟨99451867519541127148061305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132602490026054836197415073 99451867519541127148061305)
  ·
    refine ⟨74588900639655845361045979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99451867519541127148061305 74588900639655845361045979)
    ·
      refine ⟨111883350959483768041568969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74588900639655845361045979 111883350959483768041568969)
      ·
        refine ⟨83912513219612826031176727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111883350959483768041568969 83912513219612826031176727)
        ·
          refine ⟨125868769829419239046765091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83912513219612826031176727 125868769829419239046765091)
          ·
            refine ⟨188803154744128858570147637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125868769829419239046765091 188803154744128858570147637)
            ·
              refine ⟨17700295757262080490951341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188803154744128858570147637 17700295757262080490951341)
              ·
                refine ⟨6637610908973280184106753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17700295757262080490951341 6637610908973280184106753)
                ·
                  refine ⟨4978208181729960138080065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6637610908973280184106753 4978208181729960138080065)
                  ·
                    refine ⟨3733656136297470103560049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4978208181729960138080065 3733656136297470103560049)
                    ·
                      refine ⟨2800242102223102577670037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733656136297470103560049 2800242102223102577670037)
                      ·
                        rfl

theorem cell23_5453452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_5453452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453452 prefixEnd_5453452 := by exact prefixLift 5453452
  have htrace : WordTrace (prefixWord ++ tailWord_5453452) baseStart_5453452 baseEnd_5453452 := by
    simpa [prefixWord, tailWord_5453452, baseEnd_5453452] using wordTrace_append hprefix tailTrace_5453452
  have hstable : (prefixWord ++ tailWord_5453452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453452).length < 2 ^ (prefixWord ++ tailWord_5453452).sum := by decide
  have hdescent : baseEnd_5453452 < baseStart_5453452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453461 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_5453461 : Nat := 118140960795 + 5453461 * 2 ^ 59
def prefixEnd_5453461 : Nat := 4983230072969 + 3 ^ 40 * 5453461 * 2
def baseEnd_5453461 : Nat := 2800246723548993042457495

theorem tailTrace_5453461 : CollatzResearch.WordTrace tailWord_5453461 prefixEnd_5453461 2800246723548993042457495 := by
  unfold tailWord_5453461
  simp only [CollatzResearch.WordTrace]
  refine ⟨198904063296049648833200237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132602708864033099222133491 198904063296049648833200237)
  ·
    refine ⟨74589023736018618312450089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198904063296049648833200237 74589023736018618312450089)
    ·
      refine ⟨55941767802013963734337567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74589023736018618312450089 55941767802013963734337567)
      ·
        refine ⟨83912651703020945601506351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55941767802013963734337567 83912651703020945601506351)
        ·
          refine ⟨125868977554531418402259527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83912651703020945601506351 125868977554531418402259527)
          ·
            refine ⟨188803466331797127603389291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125868977554531418402259527 188803466331797127603389291)
            ·
              refine ⟨283205199497695691405083937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188803466331797127603389291 283205199497695691405083937)
              ·
                refine ⟨212403899623271768553812953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283205199497695691405083937 212403899623271768553812953)
                ·
                  refine ⟨159302924717453826415359715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212403899623271768553812953 159302924717453826415359715)
                  ·
                    refine ⟨238954387076180739623039573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159302924717453826415359715 238954387076180739623039573)
                    ·
                      refine ⟨2800246723548993042457495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 238954387076180739623039573 2800246723548993042457495)
                      ·
                        rfl

theorem cell23_5453461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_5453461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453461 prefixEnd_5453461 := by exact prefixLift 5453461
  have htrace : WordTrace (prefixWord ++ tailWord_5453461) baseStart_5453461 baseEnd_5453461 := by
    simpa [prefixWord, tailWord_5453461, baseEnd_5453461] using wordTrace_append hprefix tailTrace_5453461
  have hstable : (prefixWord ++ tailWord_5453461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453461).length < 2 ^ (prefixWord ++ tailWord_5453461).sum := by decide
  have hdescent : baseEnd_5453461 < baseStart_5453461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453485 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_5453485 : Nat := 118140960795 + 5453485 * 2 ^ 59
def prefixEnd_5453485 : Nat := 4983230072969 + 3 ^ 40 * 5453485 * 2
def baseEnd_5453485 : Nat := 2800259047084700948557385

theorem tailTrace_5453485 : CollatzResearch.WordTrace tailWord_5453485 prefixEnd_5453485 2800259047084700948557385 := by
  unfold tailWord_5453485
  simp only [CollatzResearch.WordTrace]
  refine ⟨198904938647962700932073909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132603292431975133954715939 198904938647962700932073909)
  ·
    refine ⟨18647337998246503212381929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198904938647962700932073909 18647337998246503212381929)
    ·
      refine ⟨13985503498684877409286447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18647337998246503212381929 13985503498684877409286447)
      ·
        refine ⟨20978255248027316113929671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13985503498684877409286447 20978255248027316113929671)
        ·
          refine ⟨31467382872040974170894507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20978255248027316113929671 31467382872040974170894507)
          ·
            refine ⟨47201074308061461256341761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31467382872040974170894507 47201074308061461256341761)
            ·
              refine ⟨35400805731046095942256321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47201074308061461256341761 35400805731046095942256321)
              ·
                refine ⟨26550604298284571956692241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35400805731046095942256321 26550604298284571956692241)
                ·
                  refine ⟨19912953223713428967519181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26550604298284571956692241 19912953223713428967519181)
                  ·
                    refine ⟨7467357458892535862819693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19912953223713428967519181 7467357458892535862819693)
                    ·
                      refine ⟨2800259047084700948557385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467357458892535862819693 2800259047084700948557385)
                      ·
                        rfl

theorem cell23_5453485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_5453485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453485 prefixEnd_5453485 := by exact prefixLift 5453485
  have htrace : WordTrace (prefixWord ++ tailWord_5453485) baseStart_5453485 baseEnd_5453485 := by
    simpa [prefixWord, tailWord_5453485, baseEnd_5453485] using wordTrace_append hprefix tailTrace_5453485
  have hstable : (prefixWord ++ tailWord_5453485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453485).length < 2 ^ (prefixWord ++ tailWord_5453485).sum := by decide
  have hdescent : baseEnd_5453485 < baseStart_5453485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453488 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 2, 5]
def baseStart_5453488 : Nat := 118140960795 + 5453488 * 2 ^ 59
def prefixEnd_5453488 : Nat := 4983230072969 + 3 ^ 40 * 5453488 * 2
def baseEnd_5453488 : Nat := 933420195842221478939957

theorem tailTrace_5453488 : CollatzResearch.WordTrace tailWord_5453488 prefixEnd_5453488 933420195842221478939957 := by
  unfold tailWord_5453488
  simp only [CollatzResearch.WordTrace]
  refine ⟨99452524033475916222216559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132603365377967888296288745 99452524033475916222216559)
  ·
    refine ⟨149178786050213874333324839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99452524033475916222216559 149178786050213874333324839)
    ·
      refine ⟨223768179075320811499987259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149178786050213874333324839 223768179075320811499987259)
      ·
        refine ⟨335652268612981217249980889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223768179075320811499987259 335652268612981217249980889)
        ·
          refine ⟨251739201459735912937485667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335652268612981217249980889 251739201459735912937485667)
          ·
            refine ⟨377608802189603869406228501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251739201459735912937485667 377608802189603869406228501)
            ·
              refine ⟨17700412602637681378416961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 377608802189603869406228501 17700412602637681378416961)
              ·
                refine ⟨13275309451978261033812721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17700412602637681378416961 13275309451978261033812721)
                ·
                  refine ⟨9956482088983695775359541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13275309451978261033812721 9956482088983695775359541)
                  ·
                    refine ⟨933420195842221478939957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9956482088983695775359541 933420195842221478939957)
                    ·
                      rfl

theorem cell23_5453488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_5453488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453488 prefixEnd_5453488 := by exact prefixLift 5453488
  have htrace : WordTrace (prefixWord ++ tailWord_5453488) baseStart_5453488 baseEnd_5453488 := by
    simpa [prefixWord, tailWord_5453488, baseEnd_5453488] using wordTrace_append hprefix tailTrace_5453488
  have hstable : (prefixWord ++ tailWord_5453488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453488).length < 2 ^ (prefixWord ++ tailWord_5453488).sum := by decide
  have hdescent : baseEnd_5453488 < baseStart_5453488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453495 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 2, 5, 2]
def baseStart_5453495 : Nat := 118140960795 + 5453495 * 2 ^ 59
def prefixEnd_5453495 : Nat := 4983230072969 + 3 ^ 40 * 5453495 * 2
def baseEnd_5453495 : Nat := 2800264181891245909432339

theorem tailTrace_5453495 : CollatzResearch.WordTrace tailWord_5453495 prefixEnd_5453495 2800264181891245909432339 := by
  unfold tailWord_5453495
  simp only [CollatzResearch.WordTrace]
  refine ⟨198905303377926472639937939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132603535585284315093291959 198905303377926472639937939)
  ·
    refine ⟨298357955066889708959906909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198905303377926472639937939 298357955066889708959906909)
    ·
      refine ⟨111884233150083640859965091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298357955066889708959906909 111884233150083640859965091)
      ·
        refine ⟨167826349725125461289947637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111884233150083640859965091 167826349725125461289947637)
        ·
          refine ⟨15733720286730511995932591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167826349725125461289947637 15733720286730511995932591)
          ·
            refine ⟨23600580430095767993898887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15733720286730511995932591 23600580430095767993898887)
            ·
              refine ⟨35400870645143651990848331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23600580430095767993898887 35400870645143651990848331)
              ·
                refine ⟨53101305967715477986272497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35400870645143651990848331 53101305967715477986272497)
                ·
                  refine ⟨39825979475786608489704373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53101305967715477986272497 39825979475786608489704373)
                  ·
                    refine ⟨3733685575854994545909785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39825979475786608489704373 3733685575854994545909785)
                    ·
                      refine ⟨2800264181891245909432339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3733685575854994545909785 2800264181891245909432339)
                      ·
                        rfl

theorem cell23_5453495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_5453495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453495 prefixEnd_5453495 := by exact prefixLift 5453495
  have htrace : WordTrace (prefixWord ++ tailWord_5453495) baseStart_5453495 baseEnd_5453495 := by
    simpa [prefixWord, tailWord_5453495, baseEnd_5453495] using wordTrace_append hprefix tailTrace_5453495
  have hstable : (prefixWord ++ tailWord_5453495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453495).length < 2 ^ (prefixWord ++ tailWord_5453495).sum := by decide
  have hdescent : baseEnd_5453495 < baseStart_5453495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453498 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_5453498 : Nat := 118140960795 + 5453498 * 2 ^ 59
def prefixEnd_5453498 : Nat := 4983230072969 + 3 ^ 40 * 5453498 * 2
def baseEnd_5453498 : Nat := 2800265722333209397694825

theorem tailTrace_5453498 : CollatzResearch.WordTrace tailWord_5453498 prefixEnd_5453498 2800265722333209397694825 := by
  unfold tailWord_5453498
  simp only [CollatzResearch.WordTrace]
  refine ⟨49726353199228901038074287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132603608531277069434864765 49726353199228901038074287)
  ·
    refine ⟨74589529798843351557111431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49726353199228901038074287 74589529798843351557111431)
    ·
      refine ⟨111884294698265027335667147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74589529798843351557111431 111884294698265027335667147)
      ·
        refine ⟨167826442047397541003500721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111884294698265027335667147 167826442047397541003500721)
        ·
          refine ⟨125869831535548155752625541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167826442047397541003500721 125869831535548155752625541)
          ·
            refine ⟨23600593412915279203617289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125869831535548155752625541 23600593412915279203617289)
            ·
              refine ⟨17700445059686459402712967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23600593412915279203617289 17700445059686459402712967)
              ·
                refine ⟨26550667589529689104069451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17700445059686459402712967 26550667589529689104069451)
                ·
                  refine ⟨39826001384294533656104177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26550667589529689104069451 39826001384294533656104177)
                  ·
                    refine ⟨29869501038220900242078133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39826001384294533656104177 29869501038220900242078133)
                    ·
                      refine ⟨2800265722333209397694825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29869501038220900242078133 2800265722333209397694825)
                      ·
                        rfl

theorem cell23_5453498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_5453498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453498 prefixEnd_5453498 := by exact prefixLift 5453498
  have htrace : WordTrace (prefixWord ++ tailWord_5453498) baseStart_5453498 baseEnd_5453498 := by
    simpa [prefixWord, tailWord_5453498, baseEnd_5453498] using wordTrace_append hprefix tailTrace_5453498
  have hstable : (prefixWord ++ tailWord_5453498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453498).length < 2 ^ (prefixWord ++ tailWord_5453498).sum := by decide
  have hdescent : baseEnd_5453498 < baseStart_5453498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453522 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_5453522 : Nat := 118140960795 + 5453522 * 2 ^ 59
def prefixEnd_5453522 : Nat := 4983230072969 + 3 ^ 40 * 5453522 * 2
def baseEnd_5453522 : Nat := 933426015289639101264905

theorem tailTrace_5453522 : CollatzResearch.WordTrace tailWord_5453522 prefixEnd_5453522 933426015289639101264905 := by
  unfold tailWord_5453522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49726572037207164062792705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132604192099219104167447213 49726572037207164062792705)
  ·
    refine ⟨37294929027905373047094529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49726572037207164062792705 37294929027905373047094529)
    ·
      refine ⟨27971196770929029785320897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37294929027905373047094529 27971196770929029785320897)
      ·
        refine ⟨20978397578196772338990673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27971196770929029785320897 20978397578196772338990673)
        ·
          refine ⟨15733798183647579254243005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20978397578196772338990673 15733798183647579254243005)
          ·
            refine ⟨5900174318867842220341127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15733798183647579254243005 5900174318867842220341127)
            ·
              refine ⟨8850261478301763330511691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900174318867842220341127 8850261478301763330511691)
              ·
                refine ⟨13275392217452644995767537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8850261478301763330511691 13275392217452644995767537)
                ·
                  refine ⟨9956544163089483746825653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13275392217452644995767537 9956544163089483746825653)
                  ·
                    refine ⟨933426015289639101264905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9956544163089483746825653 933426015289639101264905)
                    ·
                      rfl

theorem cell23_5453522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_5453522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453522 prefixEnd_5453522 := by exact prefixLift 5453522
  have htrace : WordTrace (prefixWord ++ tailWord_5453522) baseStart_5453522 baseEnd_5453522 := by
    simpa [prefixWord, tailWord_5453522, baseEnd_5453522] using wordTrace_append hprefix tailTrace_5453522
  have hstable : (prefixWord ++ tailWord_5453522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453522).length < 2 ^ (prefixWord ++ tailWord_5453522).sum := by decide
  have hdescent : baseEnd_5453522 < baseStart_5453522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453526 : List Nat := [5, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_5453526 : Nat := 118140960795 + 5453526 * 2 ^ 59
def prefixEnd_5453526 : Nat := 4983230072969 + 3 ^ 40 * 5453526 * 2
def baseEnd_5453526 : Nat := 311142233310170587571633

theorem tailTrace_5453526 : CollatzResearch.WordTrace tailWord_5453526 prefixEnd_5453526 311142233310170587571633 := by
  unfold tailWord_5453526
  simp only [CollatzResearch.WordTrace]
  refine ⟨12431652127550885308394777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132604289360542776622877621 12431652127550885308394777)
  ·
    refine ⟨9323739095663163981296083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12431652127550885308394777 9323739095663163981296083)
    ·
      refine ⟨13985608643494745971944125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9323739095663163981296083 13985608643494745971944125)
      ·
        refine ⟨5244603241310529739479047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13985608643494745971944125 5244603241310529739479047)
        ·
          refine ⟨7866904861965794609218571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244603241310529739479047 7866904861965794609218571)
          ·
            refine ⟨11800357292948691913827857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7866904861965794609218571 11800357292948691913827857)
            ·
              refine ⟨8850267969711518935370893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11800357292948691913827857 8850267969711518935370893)
              ·
                refine ⟨3318850488641819600764085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8850267969711518935370893 3318850488641819600764085)
                ·
                  refine ⟨311142233310170587571633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3318850488641819600764085 311142233310170587571633)
                  ·
                    rfl

theorem cell23_5453526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_5453526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453526 prefixEnd_5453526 := by exact prefixLift 5453526
  have htrace : WordTrace (prefixWord ++ tailWord_5453526) baseStart_5453526 baseEnd_5453526 := by
    simpa [prefixWord, tailWord_5453526, baseEnd_5453526] using wordTrace_append hprefix tailTrace_5453526
  have hstable : (prefixWord ++ tailWord_5453526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453526).length < 2 ^ (prefixWord ++ tailWord_5453526).sum := by decide
  have hdescent : baseEnd_5453526 < baseStart_5453526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453586 : List Nat := [3, 2, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_5453586 : Nat := 118140960795 + 5453586 * 2 ^ 59
def prefixEnd_5453586 : Nat := 4983230072969 + 3 ^ 40 * 5453586 * 2
def baseEnd_5453586 : Nat := 933436969543601684464807

theorem tailTrace_5453586 : CollatzResearch.WordTrace tailWord_5453586 prefixEnd_5453586 933436969543601684464807 := by
  unfold tailWord_5453586
  simp only [CollatzResearch.WordTrace]
  refine ⟨49727155605149198795375153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132605748280397863454333741 49727155605149198795375153)
  ·
    refine ⟨37295366703861899096531365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49727155605149198795375153 37295366703861899096531365)
    ·
      refine ⟨6992881256974106080599631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37295366703861899096531365 6992881256974106080599631)
      ·
        refine ⟨10489321885461159120899447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992881256974106080599631 10489321885461159120899447)
        ·
          refine ⟨15733982828191738681349171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10489321885461159120899447 15733982828191738681349171)
          ·
            refine ⟨23600974242287608022023757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15733982828191738681349171 23600974242287608022023757)
            ·
              refine ⟨8850365340857853008258909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23600974242287608022023757 8850365340857853008258909)
              ·
                refine ⟨3318887002821694878097091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8850365340857853008258909 3318887002821694878097091)
                ·
                  refine ⟨4978330504232542317145637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318887002821694878097091 4978330504232542317145637)
                  ·
                    refine ⟨933436969543601684464807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4978330504232542317145637 933436969543601684464807)
                    ·
                      rfl

theorem cell23_5453586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_5453586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453586 prefixEnd_5453586 := by exact prefixLift 5453586
  have htrace : WordTrace (prefixWord ++ tailWord_5453586) baseStart_5453586 baseEnd_5453586 := by
    simpa [prefixWord, tailWord_5453586, baseEnd_5453586] using wordTrace_append hprefix tailTrace_5453586
  have hstable : (prefixWord ++ tailWord_5453586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453586).length < 2 ^ (prefixWord ++ tailWord_5453586).sum := by decide
  have hdescent : baseEnd_5453586 < baseStart_5453586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453629 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_5453629 : Nat := 118140960795 + 5453629 * 2 ^ 59
def prefixEnd_5453629 : Nat := 4983230072969 + 3 ^ 40 * 5453629 * 2
def baseEnd_5453629 : Nat := 933444329432982795052241

theorem tailTrace_5453629 : CollatzResearch.WordTrace tailWord_5453629 prefixEnd_5453629 933444329432982795052241 := by
  unfold tailWord_5453629
  simp only [CollatzResearch.WordTrace]
  refine ⟨198910190759441013525315941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132606793839627342350210627 198910190759441013525315941)
  ·
    refine ⟨37295660767395190035996739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198910190759441013525315941 37295660767395190035996739)
    ·
      refine ⟨55943491151092785053995109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37295660767395190035996739 55943491151092785053995109)
      ·
        refine ⟨10489404590829897197624083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55943491151092785053995109 10489404590829897197624083)
        ·
          refine ⟨15734106886244845796436125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10489404590829897197624083 15734106886244845796436125)
          ·
            refine ⟨5900290082341817173663547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15734106886244845796436125 5900290082341817173663547)
            ·
              refine ⟨8850435123512725760495321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900290082341817173663547 8850435123512725760495321)
              ·
                refine ⟨6637826342634544320371491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8850435123512725760495321 6637826342634544320371491)
                ·
                  refine ⟨9956739513951816480557237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6637826342634544320371491 9956739513951816480557237)
                  ·
                    refine ⟨933444329432982795052241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9956739513951816480557237 933444329432982795052241)
                    ·
                      rfl

theorem cell23_5453629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_5453629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453629 prefixEnd_5453629 := by exact prefixLift 5453629
  have htrace : WordTrace (prefixWord ++ tailWord_5453629) baseStart_5453629 baseEnd_5453629 := by
    simpa [prefixWord, tailWord_5453629, baseEnd_5453629] using wordTrace_append hprefix tailTrace_5453629
  have hstable : (prefixWord ++ tailWord_5453629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453629).length < 2 ^ (prefixWord ++ tailWord_5453629).sum := by decide
  have hdescent : baseEnd_5453629 < baseStart_5453629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453649 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 1, 1, 4]
def baseStart_5453649 : Nat := 118140960795 + 5453649 * 2 ^ 59
def prefixEnd_5453649 : Nat := 4983230072969 + 3 ^ 40 * 5453649 * 2
def baseEnd_5453649 : Nat := 2800343257912038306906631

theorem tailTrace_5453649 : CollatzResearch.WordTrace tailWord_5453649 prefixEnd_5453649 2800343257912038306906631 := by
  unfold tailWord_5453649
  simp only [CollatzResearch.WordTrace]
  refine ⟨198910920219368556941044001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132607280146245704627362667 198910920219368556941044001)
  ·
    refine ⟨149183190164526417705783001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198910920219368556941044001 149183190164526417705783001)
    ·
      refine ⟨111887392623394813279337251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149183190164526417705783001 111887392623394813279337251)
      ·
        refine ⟨167831088935092219919005877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111887392623394813279337251 167831088935092219919005877)
        ·
          refine ⟨15734164587664895617406801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167831088935092219919005877 15734164587664895617406801)
          ·
            refine ⟨11800623440748671713055101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15734164587664895617406801 11800623440748671713055101)
            ·
              refine ⟨4425233790280751892395663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11800623440748671713055101 4425233790280751892395663)
              ·
                refine ⟨6637850685421127838593495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425233790280751892395663 6637850685421127838593495)
                ·
                  refine ⟨9956776028131691757890243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6637850685421127838593495 9956776028131691757890243)
                  ·
                    refine ⟨14935164042197537636835365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9956776028131691757890243 14935164042197537636835365)
                    ·
                      refine ⟨2800343257912038306906631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14935164042197537636835365 2800343257912038306906631)
                      ·
                        rfl

theorem cell23_5453649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_5453649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453649 prefixEnd_5453649 := by exact prefixLift 5453649
  have htrace : WordTrace (prefixWord ++ tailWord_5453649) baseStart_5453649 baseEnd_5453649 := by
    simpa [prefixWord, tailWord_5453649, baseEnd_5453649] using wordTrace_append hprefix tailTrace_5453649
  have hstable : (prefixWord ++ tailWord_5453649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453649).length < 2 ^ (prefixWord ++ tailWord_5453649).sum := by decide
  have hdescent : baseEnd_5453649 < baseStart_5453649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453652 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_5453652 : Nat := 118140960795 + 5453652 * 2 ^ 59
def prefixEnd_5453652 : Nat := 4983230072969 + 3 ^ 40 * 5453652 * 2
def baseEnd_5453652 : Nat := 2800344798354001795169117

theorem tailTrace_5453652 : CollatzResearch.WordTrace tailWord_5453652 prefixEnd_5453652 2800344798354001795169117 := by
  unfold tailWord_5453652
  simp only [CollatzResearch.WordTrace]
  refine ⟨99455514819178844226701605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132607353092238458968935473 99455514819178844226701605)
  ·
    refine ⟨18647909028596033292506551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99455514819178844226701605 18647909028596033292506551)
    ·
      refine ⟨27971863542894049938759827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18647909028596033292506551 27971863542894049938759827)
      ·
        refine ⟨41957795314341074908139741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27971863542894049938759827 41957795314341074908139741)
        ·
          refine ⟨15734173242877903090552403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41957795314341074908139741 15734173242877903090552403)
          ·
            refine ⟨23601259864316854635828605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15734173242877903090552403 23601259864316854635828605)
            ·
              refine ⟨8850472449118820488435727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23601259864316854635828605 8850472449118820488435727)
              ·
                refine ⟨13275708673678230732653591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8850472449118820488435727 13275708673678230732653591)
                ·
                  refine ⟨19913563010517346098980387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13275708673678230732653591 19913563010517346098980387)
                  ·
                    refine ⟨29870344515776019148470581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19913563010517346098980387 29870344515776019148470581)
                    ·
                      refine ⟨2800344798354001795169117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29870344515776019148470581 2800344798354001795169117)
                      ·
                        rfl

theorem cell23_5453652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_5453652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453652 prefixEnd_5453652 := by exact prefixLift 5453652
  have htrace : WordTrace (prefixWord ++ tailWord_5453652) baseStart_5453652 baseEnd_5453652 := by
    simpa [prefixWord, tailWord_5453652, baseEnd_5453652] using wordTrace_append hprefix tailTrace_5453652
  have hstable : (prefixWord ++ tailWord_5453652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453652).length < 2 ^ (prefixWord ++ tailWord_5453652).sum := by decide
  have hdescent : baseEnd_5453652 < baseStart_5453652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453655 : List Nat := [1, 1, 3, 2, 6, 10]
def baseStart_5453655 : Nat := 118140960795 + 5453655 * 2 ^ 59
def prefixEnd_5453655 : Nat := 4983230072969 + 3 ^ 40 * 5453655 * 2
def baseEnd_5453655 : Nat := 11524059007390803635521

theorem tailTrace_5453655 : CollatzResearch.WordTrace tailWord_5453655 prefixEnd_5453655 11524059007390803635521 := by
  unfold tailWord_5453655
  simp only [CollatzResearch.WordTrace]
  refine ⟨198911139057346819965762419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132607426038231213310508279 198911139057346819965762419)
  ·
    refine ⟨298366708586020229948643629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198911139057346819965762419 298366708586020229948643629)
    ·
      refine ⟨111887515719757586230741361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298366708586020229948643629 111887515719757586230741361)
      ·
        refine ⟨83915636789818189673056021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111887515719757586230741361 83915636789818189673056021)
        ·
          refine ⟨3933545474522727640924501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83915636789818189673056021 3933545474522727640924501)
          ·
            refine ⟨11524059007390803635521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3933545474522727640924501 11524059007390803635521)
            ·
              rfl

theorem cell23_5453655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 10].length) (baseStart_5453655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453655 prefixEnd_5453655 := by exact prefixLift 5453655
  have htrace : WordTrace (prefixWord ++ tailWord_5453655) baseStart_5453655 baseEnd_5453655 := by
    simpa [prefixWord, tailWord_5453655, baseEnd_5453655] using wordTrace_append hprefix tailTrace_5453655
  have hstable : (prefixWord ++ tailWord_5453655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453655).length < 2 ^ (prefixWord ++ tailWord_5453655).sum := by decide
  have hdescent : baseEnd_5453655 < baseStart_5453655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453660 : List Nat := [2, 2, 4, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_5453660 : Nat := 118140960795 + 5453660 * 2 ^ 59
def prefixEnd_5453660 : Nat := 4983230072969 + 3 ^ 40 * 5453660 * 2
def baseEnd_5453660 : Nat := 2800348906199237763869081

theorem tailTrace_5453660 : CollatzResearch.WordTrace tailWord_5453660 prefixEnd_5453660 2800348906199237763869081 := by
  unfold tailWord_5453660
  simp only [CollatzResearch.WordTrace]
  refine ⟨99455660711164352909847217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132607547614885803879796289 99455660711164352909847217)
  ·
    refine ⟨74591745533373264682385413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99455660711164352909847217 74591745533373264682385413)
    ·
      refine ⟨13985952287507487127947265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74591745533373264682385413 13985952287507487127947265)
      ·
        refine ⟨10489464215630615345960449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13985952287507487127947265 10489464215630615345960449)
        ·
          refine ⟨7867098161722961509470337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10489464215630615345960449 7867098161722961509470337)
          ·
            refine ⟨5900323621292221132102753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7867098161722961509470337 5900323621292221132102753)
            ·
              refine ⟨4425242715969165849077065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5900323621292221132102753 4425242715969165849077065)
              ·
                refine ⟨3318932036976874386807799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4425242715969165849077065 3318932036976874386807799)
                ·
                  refine ⟨4978398055465311580211699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318932036976874386807799 4978398055465311580211699)
                  ·
                    refine ⟨7467597083197967370317549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4978398055465311580211699 7467597083197967370317549)
                    ·
                      refine ⟨2800348906199237763869081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467597083197967370317549 2800348906199237763869081)
                      ·
                        rfl

theorem cell23_5453660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_5453660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453660 prefixEnd_5453660 := by exact prefixLift 5453660
  have htrace : WordTrace (prefixWord ++ tailWord_5453660) baseStart_5453660 baseEnd_5453660 := by
    simpa [prefixWord, tailWord_5453660, baseEnd_5453660] using wordTrace_append hprefix tailTrace_5453660
  have hstable : (prefixWord ++ tailWord_5453660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453660).length < 2 ^ (prefixWord ++ tailWord_5453660).sum := by decide
  have hdescent : baseEnd_5453660 < baseStart_5453660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453665 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_5453665 : Nat := 118140960795 + 5453665 * 2 ^ 59
def prefixEnd_5453665 : Nat := 4983230072969 + 3 ^ 40 * 5453665 * 2
def baseEnd_5453665 : Nat := 2800351473602510244306557

theorem tailTrace_5453665 : CollatzResearch.WordTrace tailWord_5453665 prefixEnd_5453665 2800351473602510244306557 := by
  unfold tailWord_5453665
  simp only [CollatzResearch.WordTrace]
  refine ⟨198911503787310591673626449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132607669191540394449084299 198911503787310591673626449)
  ·
    refine ⟨149183627840482943755219837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198911503787310591673626449 149183627840482943755219837)
    ·
      refine ⟨55943860440181103908207439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149183627840482943755219837 55943860440181103908207439)
      ·
        refine ⟨83915790660271655862311159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55943860440181103908207439 83915790660271655862311159)
        ·
          refine ⟨125873685990407483793466739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83915790660271655862311159 125873685990407483793466739)
          ·
            refine ⟨188810528985611225690200109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125873685990407483793466739 188810528985611225690200109)
            ·
              refine ⟨70803948369604209633825041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188810528985611225690200109 70803948369604209633825041)
              ·
                refine ⟨53102961277203157225368781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70803948369604209633825041 53102961277203157225368781)
                ·
                  refine ⟨19913610478951183959513293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53102961277203157225368781 19913610478951183959513293)
                  ·
                    refine ⟨7467603929606693984817485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19913610478951183959513293 7467603929606693984817485)
                    ·
                      refine ⟨2800351473602510244306557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467603929606693984817485 2800351473602510244306557)
                      ·
                        rfl

theorem cell23_5453665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_5453665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453665 prefixEnd_5453665 := by exact prefixLift 5453665
  have htrace : WordTrace (prefixWord ++ tailWord_5453665) baseStart_5453665 baseEnd_5453665 := by
    simpa [prefixWord, tailWord_5453665, baseEnd_5453665] using wordTrace_append hprefix tailTrace_5453665
  have hstable : (prefixWord ++ tailWord_5453665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453665).length < 2 ^ (prefixWord ++ tailWord_5453665).sum := by decide
  have hdescent : baseEnd_5453665 < baseStart_5453665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453682 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_5453682 : Nat := 118140960795 + 5453682 * 2 ^ 59
def prefixEnd_5453682 : Nat := 4983230072969 + 3 ^ 40 * 5453682 * 2
def baseEnd_5453682 : Nat := 2800360202773636677793979

theorem tailTrace_5453682 : CollatzResearch.WordTrace tailWord_5453682 prefixEnd_5453682 2800360202773636677793979 := by
  unfold tailWord_5453682
  simp only [CollatzResearch.WordTrace]
  refine ⟨49728030957062250894248825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132608082552166002384663533 49728030957062250894248825)
  ·
    refine ⟨37296023217796688170686619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49728030957062250894248825 37296023217796688170686619)
    ·
      refine ⟨55944034826695032256029929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37296023217796688170686619 55944034826695032256029929)
      ·
        refine ⟨41958026120021274192022447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55944034826695032256029929 41958026120021274192022447)
        ·
          refine ⟨62937039180031911288033671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41958026120021274192022447 62937039180031911288033671)
          ·
            refine ⟨94405558770047866932050507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62937039180031911288033671 94405558770047866932050507)
            ·
              refine ⟨141608338155071800398075761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94405558770047866932050507 141608338155071800398075761)
              ·
                refine ⟨106206253616303850298556821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141608338155071800398075761 106206253616303850298556821)
                ·
                  refine ⟨4978418138264242982744851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106206253616303850298556821 4978418138264242982744851)
                  ·
                    refine ⟨7467627207396364474117277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4978418138264242982744851 7467627207396364474117277)
                    ·
                      refine ⟨2800360202773636677793979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467627207396364474117277 2800360202773636677793979)
                      ·
                        rfl

theorem cell23_5453682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_5453682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453682 prefixEnd_5453682 := by exact prefixLift 5453682
  have htrace : WordTrace (prefixWord ++ tailWord_5453682) baseStart_5453682 baseEnd_5453682 := by
    simpa [prefixWord, tailWord_5453682, baseEnd_5453682] using wordTrace_append hprefix tailTrace_5453682
  have hstable : (prefixWord ++ tailWord_5453682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453682).length < 2 ^ (prefixWord ++ tailWord_5453682).sum := by decide
  have hdescent : baseEnd_5453682 < baseStart_5453682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453685 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_5453685 : Nat := 118140960795 + 5453685 * 2 ^ 59
def prefixEnd_5453685 : Nat := 4983230072969 + 3 ^ 40 * 5453685 * 2
def baseEnd_5453685 : Nat := 933453914405200055352155

theorem tailTrace_5453685 : CollatzResearch.WordTrace tailWord_5453685 prefixEnd_5453685 933453914405200055352155 := by
  unfold tailWord_5453685
  simp only [CollatzResearch.WordTrace]
  refine ⟨198912233247238135089354509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132608155498158756726236339 198912233247238135089354509)
  ·
    refine ⟨74592087467714300658507941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198912233247238135089354509 74592087467714300658507941)
    ·
      refine ⟨13986016400196431373470239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74592087467714300658507941 13986016400196431373470239)
      ·
        refine ⟨20979024600294647060205359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13986016400196431373470239 20979024600294647060205359)
        ·
          refine ⟨31468536900441970590308039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20979024600294647060205359 31468536900441970590308039)
          ·
            refine ⟨47202805350662955885462059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31468536900441970590308039 47202805350662955885462059)
            ·
              refine ⟨70804208025994433828193089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47202805350662955885462059 70804208025994433828193089)
              ·
                refine ⟨53103156019495825371144817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70804208025994433828193089 53103156019495825371144817)
                ·
                  refine ⟨39827367014621869028358613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53103156019495825371144817 39827367014621869028358613)
                  ·
                    refine ⟨933453914405200055352155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39827367014621869028358613 933453914405200055352155)
                    ·
                      rfl

theorem cell23_5453685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_5453685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453685 prefixEnd_5453685 := by exact prefixLift 5453685
  have htrace : WordTrace (prefixWord ++ tailWord_5453685) baseStart_5453685 baseEnd_5453685 := by
    simpa [prefixWord, tailWord_5453685, baseEnd_5453685] using wordTrace_append hprefix tailTrace_5453685
  have hstable : (prefixWord ++ tailWord_5453685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453685).length < 2 ^ (prefixWord ++ tailWord_5453685).sum := by decide
  have hdescent : baseEnd_5453685 < baseStart_5453685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453703 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_5453703 : Nat := 118140960795 + 5453703 * 2 ^ 59
def prefixEnd_5453703 : Nat := 4983230072969 + 3 ^ 40 * 5453703 * 2
def baseEnd_5453703 : Nat := 2800370985867381095631383

theorem tailTrace_5453703 : CollatzResearch.WordTrace tailWord_5453703 prefixEnd_5453703 2800370985867381095631383 := by
  unfold tailWord_5453703
  simp only [CollatzResearch.WordTrace]
  refine ⟨198912889761172924163509763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132608593174115282775673175 198912889761172924163509763)
  ·
    refine ⟨298369334641759386245264645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198912889761172924163509763 298369334641759386245264645)
    ·
      refine ⟨55944250245329884920987121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298369334641759386245264645 55944250245329884920987121)
      ·
        refine ⟨41958187683997413690740341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55944250245329884920987121 41958187683997413690740341)
        ·
          refine ⟨3933580095374757533506907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41958187683997413690740341 3933580095374757533506907)
          ·
            refine ⟨5900370143062136300260361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933580095374757533506907 5900370143062136300260361)
            ·
              refine ⟨4425277607296602225195271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5900370143062136300260361 4425277607296602225195271)
              ·
                refine ⟨6637916410944903337792907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425277607296602225195271 6637916410944903337792907)
                ·
                  refine ⟨9956874616417355006689361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6637916410944903337792907 9956874616417355006689361)
                  ·
                    refine ⟨7467655962313016255017021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9956874616417355006689361 7467655962313016255017021)
                    ·
                      refine ⟨2800370985867381095631383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467655962313016255017021 2800370985867381095631383)
                      ·
                        rfl

theorem cell23_5453703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_5453703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453703 prefixEnd_5453703 := by exact prefixLift 5453703
  have htrace : WordTrace (prefixWord ++ tailWord_5453703) baseStart_5453703 baseEnd_5453703 := by
    simpa [prefixWord, tailWord_5453703, baseEnd_5453703] using wordTrace_append hprefix tailTrace_5453703
  have hstable : (prefixWord ++ tailWord_5453703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453703).length < 2 ^ (prefixWord ++ tailWord_5453703).sum := by decide
  have hdescent : baseEnd_5453703 < baseStart_5453703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453716 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_5453716 : Nat := 118140960795 + 5453716 * 2 ^ 59
def prefixEnd_5453716 : Nat := 4983230072969 + 3 ^ 40 * 5453716 * 2
def baseEnd_5453716 : Nat := 2800377661115889544768823

theorem tailTrace_5453716 : CollatzResearch.WordTrace tailWord_5453716 prefixEnd_5453716 2800377661115889544768823 := by
  unfold tailWord_5453716
  simp only [CollatzResearch.WordTrace]
  refine ⟨99456681955062913691866501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132608909273417218255822001 99456681955062913691866501)
  ·
    refine ⟨18648127866574296317224969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99456681955062913691866501 18648127866574296317224969)
    ·
      refine ⟨13986095899930722237918727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18648127866574296317224969 13986095899930722237918727)
      ·
        refine ⟨20979143849896083356878091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13986095899930722237918727 20979143849896083356878091)
        ·
          refine ⟨31468715774844125035317137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20979143849896083356878091 31468715774844125035317137)
          ·
            refine ⟨23601536831133093776487853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31468715774844125035317137 23601536831133093776487853)
            ·
              refine ⟨8850576311674910166182945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23601536831133093776487853 8850576311674910166182945)
              ·
                refine ⟨6637932233756182624637209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8850576311674910166182945 6637932233756182624637209)
                ·
                  refine ⟨4978449175317136968477907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6637932233756182624637209 4978449175317136968477907)
                  ·
                    refine ⟨7467673762975705452716861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4978449175317136968477907 7467673762975705452716861)
                    ·
                      refine ⟨2800377661115889544768823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467673762975705452716861 2800377661115889544768823)
                      ·
                        rfl

theorem cell23_5453716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_5453716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453716 prefixEnd_5453716 := by exact prefixLift 5453716
  have htrace : WordTrace (prefixWord ++ tailWord_5453716) baseStart_5453716 baseEnd_5453716 := by
    simpa [prefixWord, tailWord_5453716, baseEnd_5453716] using wordTrace_append hprefix tailTrace_5453716
  have hstable : (prefixWord ++ tailWord_5453716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453716).length < 2 ^ (prefixWord ++ tailWord_5453716).sum := by decide
  have hdescent : baseEnd_5453716 < baseStart_5453716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453755 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 3]
def baseStart_5453755 : Nat := 118140960795 + 5453755 * 2 ^ 59
def prefixEnd_5453755 : Nat := 4983230072969 + 3 ^ 40 * 5453755 * 2
def baseEnd_5453755 : Nat := 2800397686861414892181143

theorem tailTrace_5453755 : CollatzResearch.WordTrace tailWord_5453755 prefixEnd_5453755 2800397686861414892181143 := by
  unfold tailWord_5453755
  simp only [CollatzResearch.WordTrace]
  refine ⟨198914786356984537044402719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132609857571323024696268479 198914786356984537044402719)
  ·
    refine ⟨298372179535476805566604079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198914786356984537044402719 298372179535476805566604079)
    ·
      refine ⟨447558269303215208349906119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298372179535476805566604079 447558269303215208349906119)
      ·
        refine ⟨671337403954822812524859179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447558269303215208349906119 671337403954822812524859179)
        ·
          refine ⟨1007006105932234218787288769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671337403954822812524859179 1007006105932234218787288769)
          ·
            refine ⟨755254579449175664090466577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007006105932234218787288769 755254579449175664090466577)
            ·
              refine ⟨566440934586881748067849933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755254579449175664090466577 566440934586881748067849933)
              ·
                refine ⟨212415350470080655525443725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566440934586881748067849933 212415350470080655525443725)
                ·
                  refine ⟨79655756426280245822041397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212415350470080655525443725 79655756426280245822041397)
                  ·
                    refine ⟨7467727164963773045816381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79655756426280245822041397 7467727164963773045816381)
                    ·
                      refine ⟨2800397686861414892181143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467727164963773045816381 2800397686861414892181143)
                      ·
                        rfl

theorem cell23_5453755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 3].length) (baseStart_5453755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453755 prefixEnd_5453755 := by exact prefixLift 5453755
  have htrace : WordTrace (prefixWord ++ tailWord_5453755) baseStart_5453755 baseEnd_5453755 := by
    simpa [prefixWord, tailWord_5453755, baseEnd_5453755] using wordTrace_append hprefix tailTrace_5453755
  have hstable : (prefixWord ++ tailWord_5453755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453755).length < 2 ^ (prefixWord ++ tailWord_5453755).sum := by decide
  have hdescent : baseEnd_5453755 < baseStart_5453755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453809 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 2, 5]
def baseStart_5453809 : Nat := 118140960795 + 5453809 * 2 ^ 59
def prefixEnd_5453809 : Nat := 4983230072969 + 3 ^ 40 * 5453809 * 2
def baseEnd_5453809 : Nat := 933475138272252560301965

theorem tailTrace_5453809 : CollatzResearch.WordTrace tailWord_5453809 prefixEnd_5453809 933475138272252560301965 := by
  unfold tailWord_5453809
  simp only [CollatzResearch.WordTrace]
  refine ⟨198916755898788904266868481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132611170599192602844578987 198916755898788904266868481)
  ·
    refine ⟨149187566924091678200151361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198916755898788904266868481 149187566924091678200151361)
    ·
      refine ⟨111890675193068758650113521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149187566924091678200151361 111890675193068758650113521)
      ·
        refine ⟨83918006394801568987585141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111890675193068758650113521 83918006394801568987585141)
        ·
          refine ⟨7867313099512647092586107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83918006394801568987585141 7867313099512647092586107)
          ·
            refine ⟨11800969649268970638879161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7867313099512647092586107 11800969649268970638879161)
            ·
              refine ⟨8850727236951727979159371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11800969649268970638879161 8850727236951727979159371)
              ·
                refine ⟨13276090855427591968739057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8850727236951727979159371 13276090855427591968739057)
                ·
                  refine ⟨9957068141570693976554293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13276090855427591968739057 9957068141570693976554293)
                  ·
                    refine ⟨933475138272252560301965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9957068141570693976554293 933475138272252560301965)
                    ·
                      rfl

theorem cell23_5453809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_5453809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453809 prefixEnd_5453809 := by exact prefixLift 5453809
  have htrace : WordTrace (prefixWord ++ tailWord_5453809) baseStart_5453809 baseEnd_5453809 := by
    simpa [prefixWord, tailWord_5453809, baseEnd_5453809] using wordTrace_append hprefix tailTrace_5453809
  have hstable : (prefixWord ++ tailWord_5453809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453809).length < 2 ^ (prefixWord ++ tailWord_5453809).sum := by decide
  have hdescent : baseEnd_5453809 < baseStart_5453809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453863 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5453863 : Nat := 118140960795 + 5453863 * 2 ^ 59
def prefixEnd_5453863 : Nat := 4983230072969 + 3 ^ 40 * 5453863 * 2
def baseEnd_5453863 : Nat := 2800453142772100469630647

theorem tailTrace_5453863 : CollatzResearch.WordTrace tailWord_5453863 prefixEnd_5453863 2800453142772100469630647 := by
  unfold tailWord_5453863
  simp only [CollatzResearch.WordTrace]
  refine ⟨198918725440593271489334243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132612483627062180992889495 198918725440593271489334243)
  ·
    refine ⟨298378088160889907234001365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198918725440593271489334243 298378088160889907234001365)
    ·
      refine ⟨6993236441270857200796907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 298378088160889907234001365 6993236441270857200796907)
      ·
        refine ⟨10489854661906285801195361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993236441270857200796907 10489854661906285801195361)
        ·
          refine ⟨7867390996429714350896521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10489854661906285801195361 7867390996429714350896521)
          ·
            refine ⟨5900543247322285763172391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7867390996429714350896521 5900543247322285763172391)
            ·
              refine ⟨8850814870983428644758587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900543247322285763172391 8850814870983428644758587)
              ·
                refine ⟨13276222306475142967137881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8850814870983428644758587 13276222306475142967137881)
                ·
                  refine ⟨9957166729856357225353411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13276222306475142967137881 9957166729856357225353411)
                  ·
                    refine ⟨14935750094784535838030117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9957166729856357225353411 14935750094784535838030117)
                    ·
                      refine ⟨2800453142772100469630647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14935750094784535838030117 2800453142772100469630647)
                      ·
                        rfl

theorem cell23_5453863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5453863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453863 prefixEnd_5453863 := by exact prefixLift 5453863
  have htrace : WordTrace (prefixWord ++ tailWord_5453863) baseStart_5453863 baseEnd_5453863 := by
    simpa [prefixWord, tailWord_5453863, baseEnd_5453863] using wordTrace_append hprefix tailTrace_5453863
  have hstable : (prefixWord ++ tailWord_5453863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453863).length < 2 ^ (prefixWord ++ tailWord_5453863).sum := by decide
  have hdescent : baseEnd_5453863 < baseStart_5453863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453866 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_5453866 : Nat := 118140960795 + 5453866 * 2 ^ 59
def prefixEnd_5453866 : Nat := 4983230072969 + 3 ^ 40 * 5453866 * 2
def baseEnd_5453866 : Nat := 2800454683214063957893133

theorem tailTrace_5453866 : CollatzResearch.WordTrace tailWord_5453866 prefixEnd_5453866 2800454683214063957893133 := by
  unfold tailWord_5453866
  simp only [CollatzResearch.WordTrace]
  refine ⟨49729708714895600750423363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132612556573054935334462301 49729708714895600750423363)
  ·
    refine ⟨74594563072343401125635045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49729708714895600750423363 74594563072343401125635045)
    ·
      refine ⟨13986480576064387711056571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74594563072343401125635045 13986480576064387711056571)
      ·
        refine ⟨20979720864096581566584857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13986480576064387711056571 20979720864096581566584857)
        ·
          refine ⟨15734790648072436174938643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20979720864096581566584857 15734790648072436174938643)
          ·
            refine ⟨23602185972108654262407965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15734790648072436174938643 23602185972108654262407965)
            ·
              refine ⟨8850819739540745348402987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23602185972108654262407965 8850819739540745348402987)
              ·
                refine ⟨13276229609311118022604481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8850819739540745348402987 13276229609311118022604481)
                ·
                  refine ⟨9957172206983338516953361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13276229609311118022604481 9957172206983338516953361)
                  ·
                    refine ⟨7467879155237503887715021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9957172206983338516953361 7467879155237503887715021)
                    ·
                      refine ⟨2800454683214063957893133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7467879155237503887715021 2800454683214063957893133)
                      ·
                        rfl

theorem cell23_5453866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_5453866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453866 prefixEnd_5453866 := by exact prefixLift 5453866
  have htrace : WordTrace (prefixWord ++ tailWord_5453866) baseStart_5453866 baseEnd_5453866 := by
    simpa [prefixWord, tailWord_5453866, baseEnd_5453866] using wordTrace_append hprefix tailTrace_5453866
  have hstable : (prefixWord ++ tailWord_5453866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453866).length < 2 ^ (prefixWord ++ tailWord_5453866).sum := by decide
  have hdescent : baseEnd_5453866 < baseStart_5453866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453916 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5453916 : Nat := 118140960795 + 5453916 * 2 ^ 59
def prefixEnd_5453916 : Nat := 4983230072969 + 3 ^ 40 * 5453916 * 2
def baseEnd_5453916 : Nat := 933493452415596254089301

theorem tailTrace_5453916 : CollatzResearch.WordTrace tailWord_5453916 prefixEnd_5453916 933493452415596254089301 := by
  unfold tailWord_5453916
  simp only [CollatzResearch.WordTrace]
  refine ⟨99460329254700630770506801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132613772339600841027342401 99460329254700630770506801)
  ·
    refine ⟨74595246941025473077880101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99460329254700630770506801 74595246941025473077880101)
    ·
      refine ⟨13986608801442276202102519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74595246941025473077880101 13986608801442276202102519)
      ·
        refine ⟨20979913202163414303153779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13986608801442276202102519 20979913202163414303153779)
        ·
          refine ⟨31469869803245121454730669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20979913202163414303153779 31469869803245121454730669)
          ·
            refine ⟨11801201176216920545524001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31469869803245121454730669 11801201176216920545524001)
            ·
              refine ⟨8850900882162690409143001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11801201176216920545524001 8850900882162690409143001)
              ·
                refine ⟨6638175661622017806857251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8850900882162690409143001 6638175661622017806857251)
                ·
                  refine ⟨9957263492433026710285877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6638175661622017806857251 9957263492433026710285877)
                  ·
                    refine ⟨933493452415596254089301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9957263492433026710285877 933493452415596254089301)
                    ·
                      rfl

theorem cell23_5453916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5453916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453916 prefixEnd_5453916 := by exact prefixLift 5453916
  have htrace : WordTrace (prefixWord ++ tailWord_5453916) baseStart_5453916 baseEnd_5453916 := by
    simpa [prefixWord, tailWord_5453916, baseEnd_5453916] using wordTrace_append hprefix tailTrace_5453916
  have hstable : (prefixWord ++ tailWord_5453916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453916).length < 2 ^ (prefixWord ++ tailWord_5453916).sum := by decide
  have hdescent : baseEnd_5453916 < baseStart_5453916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5453986 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_5453986 : Nat := 118140960795 + 5453986 * 2 ^ 59
def prefixEnd_5453986 : Nat := 4983230072969 + 3 ^ 40 * 5453986 * 2
def baseEnd_5453986 : Nat := 2800516300892603488392581

theorem tailTrace_5453986 : CollatzResearch.WordTrace tailWord_5453986 prefixEnd_5453986 2800516300892603488392581 := by
  unfold tailWord_5453986
  simp only [CollatzResearch.WordTrace]
  refine ⟨49730802904786915874015453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132615474412765108997374541 49730802904786915874015453)
  ·
    refine ⟨18649051089295093452755795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49730802904786915874015453 18649051089295093452755795)
    ·
      refine ⟨27973576633942640179133693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18649051089295093452755795 27973576633942640179133693)
      ·
        refine ⟨10490091237728490067175135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27973576633942640179133693 10490091237728490067175135)
        ·
          refine ⟨15735136856592735100762703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10490091237728490067175135 15735136856592735100762703)
          ·
            refine ⟨23602705284889102651144055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15735136856592735100762703 23602705284889102651144055)
            ·
              refine ⟨35404057927333653976716083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23602705284889102651144055 35404057927333653976716083)
              ·
                refine ⟨53106086891000480965074125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35404057927333653976716083 53106086891000480965074125)
                ·
                  refine ⟨19914782584125180361902797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53106086891000480965074125 19914782584125180361902797)
                  ·
                    refine ⟨7468043469046942635713549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19914782584125180361902797 7468043469046942635713549)
                    ·
                      refine ⟨2800516300892603488392581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7468043469046942635713549 2800516300892603488392581)
                      ·
                        rfl

theorem cell23_5453986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_5453986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5453986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5453986 prefixEnd_5453986 := by exact prefixLift 5453986
  have htrace : WordTrace (prefixWord ++ tailWord_5453986) baseStart_5453986 baseEnd_5453986 := by
    simpa [prefixWord, tailWord_5453986, baseEnd_5453986] using wordTrace_append hprefix tailTrace_5453986
  have hstable : (prefixWord ++ tailWord_5453986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5453986).length < 2 ^ (prefixWord ++ tailWord_5453986).sum := by decide
  have hdescent : baseEnd_5453986 < baseStart_5453986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5453986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454059 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 3]
def baseStart_5454059 : Nat := 118140960795 + 5454059 * 2 ^ 59
def prefixEnd_5454059 : Nat := 4983230072969 + 3 ^ 40 * 5454059 * 2
def baseEnd_5454059 : Nat := 2800553784980381702779745

theorem tailTrace_5454059 : CollatzResearch.WordTrace tailWord_5454059 prefixEnd_5454059 2800553784980381702779745 := by
  unfold tailWord_5454059
  simp only [CollatzResearch.WordTrace]
  refine ⟨198925874147883196963469231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132617249431922131308979487 198925874147883196963469231)
  ·
    refine ⟨298388811221824795445203847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198925874147883196963469231 298388811221824795445203847)
    ·
      refine ⟨447583216832737193167805771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298388811221824795445203847 447583216832737193167805771)
      ·
        refine ⟨671374825249105789751708657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447583216832737193167805771 671374825249105789751708657)
        ·
          refine ⟨503531118936829342313781493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671374825249105789751708657 503531118936829342313781493)
          ·
            refine ⟨47206042400327750841917015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 503531118936829342313781493 47206042400327750841917015)
            ·
              refine ⟨70809063600491626262875523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47206042400327750841917015 70809063600491626262875523)
              ·
                refine ⟨106213595400737439394313285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70809063600491626262875523 106213595400737439394313285)
                ·
                  refine ⟨19915049137638269886433741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106213595400737439394313285 19915049137638269886433741)
                  ·
                    refine ⟨7468143426614351207412653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19915049137638269886433741 7468143426614351207412653)
                    ·
                      refine ⟨2800553784980381702779745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7468143426614351207412653 2800553784980381702779745)
                      ·
                        rfl

theorem cell23_5454059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 3].length) (baseStart_5454059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454059 prefixEnd_5454059 := by exact prefixLift 5454059
  have htrace : WordTrace (prefixWord ++ tailWord_5454059) baseStart_5454059 baseEnd_5454059 := by
    simpa [prefixWord, tailWord_5454059, baseEnd_5454059] using wordTrace_append hprefix tailTrace_5454059
  have hstable : (prefixWord ++ tailWord_5454059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454059).length < 2 ^ (prefixWord ++ tailWord_5454059).sum := by decide
  have hdescent : baseEnd_5454059 < baseStart_5454059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454066 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 7]
def baseStart_5454066 : Nat := 118140960795 + 5454066 * 2 ^ 59
def prefixEnd_5454066 : Nat := 4983230072969 + 3 ^ 40 * 5454066 * 2
def baseEnd_5454066 : Nat := 311173042149440352821357

theorem tailTrace_5454066 : CollatzResearch.WordTrace tailWord_5454066 prefixEnd_5454066 311173042149440352821357 := by
  unfold tailWord_5454066
  simp only [CollatzResearch.WordTrace]
  refine ⟨49731532364714459289743513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132617419639238558105982701 49731532364714459289743513)
  ·
    refine ⟨37298649273535844467307635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49731532364714459289743513 37298649273535844467307635)
    ·
      refine ⟨55947973910303766700961453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37298649273535844467307635 55947973910303766700961453)
      ·
        refine ⟨20980490216363912512860545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55947973910303766700961453 20980490216363912512860545)
        ·
          refine ⟨15735367662272934384645409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20980490216363912512860545 15735367662272934384645409)
          ·
            refine ⟨11801525746704700788484057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15735367662272934384645409 11801525746704700788484057)
            ·
              refine ⟨8851144310028525591363043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11801525746704700788484057 8851144310028525591363043)
              ·
                refine ⟨13276716465042788387044565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8851144310028525591363043 13276716465042788387044565)
                ·
                  refine ⟨311173042149440352821357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13276716465042788387044565 311173042149440352821357)
                  ·
                    rfl

theorem cell23_5454066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_5454066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454066 prefixEnd_5454066 := by exact prefixLift 5454066
  have htrace : WordTrace (prefixWord ++ tailWord_5454066) baseStart_5454066 baseEnd_5454066 := by
    simpa [prefixWord, tailWord_5454066, baseEnd_5454066] using wordTrace_append hprefix tailTrace_5454066
  have hstable : (prefixWord ++ tailWord_5454066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454066).length < 2 ^ (prefixWord ++ tailWord_5454066).sum := by decide
  have hdescent : baseEnd_5454066 < baseStart_5454066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454076 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_5454076 : Nat := 118140960795 + 5454076 * 2 ^ 59
def prefixEnd_5454076 : Nat := 4983230072969 + 3 ^ 40 * 5454076 * 2
def baseEnd_5454076 : Nat := 2800562514151508136267167

theorem tailTrace_5454076 : CollatzResearch.WordTrace tailWord_5454076 prefixEnd_5454076 2800562514151508136267167 := by
  unfold tailWord_5454076
  simp only [CollatzResearch.WordTrace]
  refine ⟨99463247094410804433419041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132617662792547739244558721 99463247094410804433419041)
  ·
    refine ⟨74597435320808103325064281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99463247094410804433419041 74597435320808103325064281)
    ·
      refine ⟨55948076490606077493798211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74597435320808103325064281 55948076490606077493798211)
      ·
        refine ⟨83922114735909116240697317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55948076490606077493798211 83922114735909116240697317)
        ·
          refine ⟨15735396512982959295130747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83922114735909116240697317 15735396512982959295130747)
          ·
            refine ⟨23603094769474438942696121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15735396512982959295130747 23603094769474438942696121)
            ·
              refine ⟨17702321077105829207022091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23603094769474438942696121 17702321077105829207022091)
              ·
                refine ⟨26553481615658743810533137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17702321077105829207022091 26553481615658743810533137)
                ·
                  refine ⟨19915111211744057857899853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26553481615658743810533137 19915111211744057857899853)
                  ·
                    refine ⟨7468166704404021696712445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19915111211744057857899853 7468166704404021696712445)
                    ·
                      refine ⟨2800562514151508136267167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7468166704404021696712445 2800562514151508136267167)
                      ·
                        rfl

theorem cell23_5454076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_5454076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454076 prefixEnd_5454076 := by exact prefixLift 5454076
  have htrace : WordTrace (prefixWord ++ tailWord_5454076) baseStart_5454076 baseEnd_5454076 := by
    simpa [prefixWord, tailWord_5454076, baseEnd_5454076] using wordTrace_append hprefix tailTrace_5454076
  have hstable : (prefixWord ++ tailWord_5454076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454076).length < 2 ^ (prefixWord ++ tailWord_5454076).sum := by decide
  have hdescent : baseEnd_5454076 < baseStart_5454076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454099 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 4]
def baseStart_5454099 : Nat := 118140960795 + 5454099 * 2 ^ 59
def prefixEnd_5454099 : Nat := 4983230072969 + 3 ^ 40 * 5454099 * 2
def baseEnd_5454099 : Nat := 2800574324206561546279561

theorem tailTrace_5454099 : CollatzResearch.WordTrace tailWord_5454099 prefixEnd_5454099 2800574324206561546279561 := by
  unfold tailWord_5454099
  simp only [CollatzResearch.WordTrace]
  refine ⟨198927333067738283794925351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132618222045158855863283567 198927333067738283794925351)
  ·
    refine ⟨298390999601607425692388027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198927333067738283794925351 298390999601607425692388027)
    ·
      refine ⟨447586499402411138538582041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298390999601607425692388027 447586499402411138538582041)
      ·
        refine ⟨335689874551808353903936531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447586499402411138538582041 335689874551808353903936531)
        ·
          refine ⟨503534811827712530855904797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335689874551808353903936531 503534811827712530855904797)
          ·
            refine ⟨188825554435392199070964299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 503534811827712530855904797 188825554435392199070964299)
            ·
              refine ⟨283238331653088298606446449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188825554435392199070964299 283238331653088298606446449)
              ·
                refine ⟨212428748739816223954834837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283238331653088298606446449 212428748739816223954834837)
                ·
                  refine ⟨9957597597178885497882883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 212428748739816223954834837 9957597597178885497882883)
                  ·
                    refine ⟨14936396395768328246824325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9957597597178885497882883 14936396395768328246824325)
                    ·
                      refine ⟨2800574324206561546279561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14936396395768328246824325 2800574324206561546279561)
                      ·
                        rfl

theorem cell23_5454099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_5454099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454099 prefixEnd_5454099 := by exact prefixLift 5454099
  have htrace : WordTrace (prefixWord ++ tailWord_5454099) baseStart_5454099 baseEnd_5454099 := by
    simpa [prefixWord, tailWord_5454099, baseEnd_5454099] using wordTrace_append hprefix tailTrace_5454099
  have hstable : (prefixWord ++ tailWord_5454099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454099).length < 2 ^ (prefixWord ++ tailWord_5454099).sum := by decide
  have hdescent : baseEnd_5454099 < baseStart_5454099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454116 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_5454116 : Nat := 118140960795 + 5454116 * 2 ^ 59
def prefixEnd_5454116 : Nat := 4983230072969 + 3 ^ 40 * 5454116 * 2
def baseEnd_5454116 : Nat := 2800583053377687979766983

theorem tailTrace_5454116 : CollatzResearch.WordTrace tailWord_5454116 prefixEnd_5454116 2800583053377687979766983 := by
  unfold tailWord_5454116
  simp only [CollatzResearch.WordTrace]
  refine ⟨99463976554338347849147101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132618635405784463798862801 99463976554338347849147101)
  ·
    refine ⟨37298991207876880443430163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99463976554338347849147101 37298991207876880443430163)
    ·
      refine ⟨55948486811815320665145245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37298991207876880443430163 55948486811815320665145245)
      ·
        refine ⟨20980682554430745249429467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55948486811815320665145245 20980682554430745249429467)
        ·
          refine ⟨31471023831646117874144201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20980682554430745249429467 31471023831646117874144201)
          ·
            refine ⟨23603267873734588405608151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31471023831646117874144201 23603267873734588405608151)
            ·
              refine ⟨35404901810601882608412227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23603267873734588405608151 35404901810601882608412227)
              ·
                refine ⟨53107352715902823912618341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35404901810601882608412227 53107352715902823912618341)
                ·
                  refine ⟨9957628634231779483615939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53107352715902823912618341 9957628634231779483615939)
                  ·
                    refine ⟨14936442951347669225423909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9957628634231779483615939 14936442951347669225423909)
                    ·
                      refine ⟨2800583053377687979766983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14936442951347669225423909 2800583053377687979766983)
                      ·
                        rfl

theorem cell23_5454116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_5454116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454116 prefixEnd_5454116 := by exact prefixLift 5454116
  have htrace : WordTrace (prefixWord ++ tailWord_5454116) baseStart_5454116 baseEnd_5454116 := by
    simpa [prefixWord, tailWord_5454116, baseEnd_5454116] using wordTrace_append hprefix tailTrace_5454116
  have hstable : (prefixWord ++ tailWord_5454116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454116).length < 2 ^ (prefixWord ++ tailWord_5454116).sum := by decide
  have hdescent : baseEnd_5454116 < baseStart_5454116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454216 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 1, 6]
def baseStart_5454216 : Nat := 118140960795 + 5454216 * 2 ^ 59
def prefixEnd_5454216 : Nat := 4983230072969 + 3 ^ 40 * 5454216 * 2
def baseEnd_5454216 : Nat := 933544800481045862838841

theorem tailTrace_5454216 : CollatzResearch.WordTrace tailWord_5454216 prefixEnd_5454216 933544800481045862838841 := by
  unfold tailWord_5454216
  simp only [CollatzResearch.WordTrace]
  refine ⟨99465800204157206388467251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132621066938876275184623001 99465800204157206388467251)
  ·
    refine ⟨149198700306235809582700877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99465800204157206388467251 149198700306235809582700877)
    ·
      refine ⟨55949512614838428593512829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149198700306235809582700877 55949512614838428593512829)
      ·
        refine ⟨20981067230564410722567311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55949512614838428593512829 20981067230564410722567311)
        ·
          refine ⟨31471600845846616083850967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20981067230564410722567311 31471600845846616083850967)
          ·
            refine ⟨47207401268769924125776451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31471600845846616083850967 47207401268769924125776451)
            ·
              refine ⟨70811101903154886188664677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47207401268769924125776451 70811101903154886188664677)
              ·
                refine ⟨13277081606841541160374627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70811101903154886188664677 13277081606841541160374627)
                ·
                  refine ⟨19915622410262311740561941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13277081606841541160374627 19915622410262311740561941)
                  ·
                    refine ⟨933544800481045862838841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19915622410262311740561941 933544800481045862838841)
                    ·
                      rfl

theorem cell23_5454216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_5454216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454216 prefixEnd_5454216 := by exact prefixLift 5454216
  have htrace : WordTrace (prefixWord ++ tailWord_5454216) baseStart_5454216 baseEnd_5454216 := by
    simpa [prefixWord, tailWord_5454216, baseEnd_5454216] using wordTrace_append hprefix tailTrace_5454216
  have hstable : (prefixWord ++ tailWord_5454216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454216).length < 2 ^ (prefixWord ++ tailWord_5454216).sum := by decide
  have hdescent : baseEnd_5454216 < baseStart_5454216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454217 : List Nat := [1, 2, 1, 1, 6, 2, 2, 3, 1, 1, 3]
def baseStart_5454217 : Nat := 118140960795 + 5454217 * 2 ^ 59
def prefixEnd_5454217 : Nat := 4983230072969 + 3 ^ 40 * 5454217 * 2
def baseEnd_5454217 : Nat := 2800634914923792084604019

theorem tailTrace_5454217 : CollatzResearch.WordTrace tailWord_5454217 prefixEnd_5454217 2800634914923792084604019 := by
  unfold tailWord_5454217
  simp only [CollatzResearch.WordTrace]
  refine ⟨198931636881310789947720905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132621091254207193298480603 198931636881310789947720905)
  ·
    refine ⟨149198727660983092460790679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198931636881310789947720905 149198727660983092460790679)
    ·
      refine ⟨223798091491474638691186019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149198727660983092460790679 223798091491474638691186019)
      ·
        refine ⟨335697137237211958036779029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223798091491474638691186019 335697137237211958036779029)
        ·
          refine ⟨15735803307994310532974017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 335697137237211958036779029 15735803307994310532974017)
          ·
            refine ⟨11801852480995732899730513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15735803307994310532974017 11801852480995732899730513)
            ·
              refine ⟨8851389360746799674797885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11801852480995732899730513 8851389360746799674797885)
              ·
                refine ⟨3319271010280049878049207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8851389360746799674797885 3319271010280049878049207)
                ·
                  refine ⟨4978906515420074817073811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319271010280049878049207 4978906515420074817073811)
                  ·
                    refine ⟨7468359773130112225610717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4978906515420074817073811 7468359773130112225610717)
                    ·
                      refine ⟨2800634914923792084604019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7468359773130112225610717 2800634914923792084604019)
                      ·
                        rfl

theorem cell23_5454217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 1, 3].length) (baseStart_5454217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454217 prefixEnd_5454217 := by exact prefixLift 5454217
  have htrace : WordTrace (prefixWord ++ tailWord_5454217) baseStart_5454217 baseEnd_5454217 := by
    simpa [prefixWord, tailWord_5454217, baseEnd_5454217] using wordTrace_append hprefix tailTrace_5454217
  have hstable : (prefixWord ++ tailWord_5454217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454217).length < 2 ^ (prefixWord ++ tailWord_5454217).sum := by decide
  have hdescent : baseEnd_5454217 < baseStart_5454217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454220 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_5454220 : Nat := 118140960795 + 5454220 * 2 ^ 59
def prefixEnd_5454220 : Nat := 4983230072969 + 3 ^ 40 * 5454220 * 2
def baseEnd_5454220 : Nat := 933545485121918524288835

theorem tailTrace_5454220 : CollatzResearch.WordTrace tailWord_5454220 prefixEnd_5454220 933545485121918524288835 := by
  unfold tailWord_5454220
  simp only [CollatzResearch.WordTrace]
  refine ⟨99465873150149960730040057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132621164200199947640053409 99465873150149960730040057)
  ·
    refine ⟨74599404862612470547530043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99465873150149960730040057 74599404862612470547530043)
    ·
      refine ⟨111899107293918705821295065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74599404862612470547530043 111899107293918705821295065)
      ·
        refine ⟨83924330470439029365971299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111899107293918705821295065 83924330470439029365971299)
        ·
          refine ⟨125886495705658544048956949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83924330470439029365971299 125886495705658544048956949)
          ·
            refine ⟨5900929486202744252294857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125886495705658544048956949 5900929486202744252294857)
            ·
              refine ⟨4425697114652058189221143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5900929486202744252294857 4425697114652058189221143)
              ·
                refine ⟨6638545671978087283831715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425697114652058189221143 6638545671978087283831715)
                ·
                  refine ⟨9957818507967130925747573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6638545671978087283831715 9957818507967130925747573)
                  ·
                    refine ⟨933545485121918524288835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9957818507967130925747573 933545485121918524288835)
                    ·
                      rfl

theorem cell23_5454220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_5454220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454220 prefixEnd_5454220 := by exact prefixLift 5454220
  have htrace : WordTrace (prefixWord ++ tailWord_5454220) baseStart_5454220 baseEnd_5454220 := by
    simpa [prefixWord, tailWord_5454220, baseEnd_5454220] using wordTrace_append hprefix tailTrace_5454220
  have hstable : (prefixWord ++ tailWord_5454220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454220).length < 2 ^ (prefixWord ++ tailWord_5454220).sum := by decide
  have hdescent : baseEnd_5454220 < baseStart_5454220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454240 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 3, 2, 2]
def baseStart_5454240 : Nat := 118140960795 + 5454240 * 2 ^ 59
def prefixEnd_5454240 : Nat := 4983230072969 + 3 ^ 40 * 5454240 * 2
def baseEnd_5454240 : Nat := 2800646724978845494616413

theorem tailTrace_5454240 : CollatzResearch.WordTrace tailWord_5454240 prefixEnd_5454240 2800646724978845494616413 := by
  unfold tailWord_5454240
  simp only [CollatzResearch.WordTrace]
  refine ⟨99466237880113732437904087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132621650506818309917205449 99466237880113732437904087)
  ·
    refine ⟨149199356820170598656856131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99466237880113732437904087 149199356820170598656856131)
    ·
      refine ⟨223799035230255897985284197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149199356820170598656856131 223799035230255897985284197)
      ·
        refine ⟨41962319105672980872240787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223799035230255897985284197 41962319105672980872240787)
        ·
          refine ⟨62943478658509471308361181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41962319105672980872240787 62943478658509471308361181)
          ·
            refine ⟨23603804496941051740635443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62943478658509471308361181 23603804496941051740635443)
            ·
              refine ⟨35405706745411577610953165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23603804496941051740635443 35405706745411577610953165)
              ·
                refine ⟨13277140029529341604107437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35405706745411577610953165 13277140029529341604107437)
                ·
                  refine ⟨4978927511073503101540289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13277140029529341604107437 4978927511073503101540289)
                  ·
                    refine ⟨3734195633305127326155217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4978927511073503101540289 3734195633305127326155217)
                    ·
                      refine ⟨2800646724978845494616413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734195633305127326155217 2800646724978845494616413)
                      ·
                        rfl

theorem cell23_5454240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_5454240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454240 prefixEnd_5454240 := by exact prefixLift 5454240
  have htrace : WordTrace (prefixWord ++ tailWord_5454240) baseStart_5454240 baseEnd_5454240 := by
    simpa [prefixWord, tailWord_5454240, baseEnd_5454240] using wordTrace_append hprefix tailTrace_5454240
  have hstable : (prefixWord ++ tailWord_5454240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454240).length < 2 ^ (prefixWord ++ tailWord_5454240).sum := by decide
  have hdescent : baseEnd_5454240 < baseStart_5454240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454263 : List Nat := [1, 1, 3, 1, 3, 5, 2, 7]
def baseStart_5454263 : Nat := 118140960795 + 5454263 * 2 ^ 59
def prefixEnd_5454263 : Nat := 4983230072969 + 3 ^ 40 * 5454263 * 2
def baseEnd_5454263 : Nat := 103728093890144403875141

theorem tailTrace_5454263 : CollatzResearch.WordTrace tailWord_5454263 prefixEnd_5454263 103728093890144403875141 := by
  unfold tailWord_5454263
  simp only [CollatzResearch.WordTrace]
  refine ⟨198933314639144139803895443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132622209759429426535930295 198933314639144139803895443)
  ·
    refine ⟨298399971958716209705843165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198933314639144139803895443 298399971958716209705843165)
    ·
      refine ⟨111899989484518578639691187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298399971958716209705843165 111899989484518578639691187)
      ·
        refine ⟨167849984226777867959536781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111899989484518578639691187 167849984226777867959536781)
        ·
          refine ⟨62943744085041700484826293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167849984226777867959536781 62943744085041700484826293)
          ·
            refine ⟨5900976007972659420452465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62943744085041700484826293 5900976007972659420452465)
            ·
              refine ⟨4425732005979494565339349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5900976007972659420452465 4425732005979494565339349)
              ·
                refine ⟨103728093890144403875141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4425732005979494565339349 103728093890144403875141)
                ·
                  rfl

theorem cell23_5454263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 7].length) (baseStart_5454263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454263 prefixEnd_5454263 := by exact prefixLift 5454263
  have htrace : WordTrace (prefixWord ++ tailWord_5454263) baseStart_5454263 baseEnd_5454263 := by
    simpa [prefixWord, tailWord_5454263, baseEnd_5454263] using wordTrace_append hprefix tailTrace_5454263
  have hstable : (prefixWord ++ tailWord_5454263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454263).length < 2 ^ (prefixWord ++ tailWord_5454263).sum := by decide
  have hdescent : baseEnd_5454263 < baseStart_5454263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454283 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 5, 3, 2]
def baseStart_5454283 : Nat := 118140960795 + 5454283 * 2 ^ 59
def prefixEnd_5454283 : Nat := 4983230072969 + 3 ^ 40 * 5454283 * 2
def baseEnd_5454283 : Nat := 2800668804646988826378715

theorem tailTrace_5454283 : CollatzResearch.WordTrace tailWord_5454283 prefixEnd_5454283 2800668804646988826378715 := by
  unfold tailWord_5454283
  simp only [CollatzResearch.WordTrace]
  refine ⟨198934044099071683219623503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132622696066047788813082335 198934044099071683219623503)
  ·
    refine ⟨298401066148607524829435255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198934044099071683219623503 298401066148607524829435255)
    ·
      refine ⟨447601599222911287244152883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298401066148607524829435255 447601599222911287244152883)
      ·
        refine ⟨671402398834366930866229325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447601599222911287244152883 671402398834366930866229325)
        ·
          refine ⟨251775899562887599074835997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 671402398834366930866229325 251775899562887599074835997)
          ·
            refine ⟨94415962336082849653063499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251775899562887599074835997 94415962336082849653063499)
            ·
              refine ⟨141623943504124274479595249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94415962336082849653063499 141623943504124274479595249)
              ·
                refine ⟨106217957628093205859696437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141623943504124274479595249 106217957628093205859696437)
                ·
                  refine ⟨9957933527633738049346541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106217957628093205859696437 9957933527633738049346541)
                  ·
                    refine ⟨3734225072862651768504953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9957933527633738049346541 3734225072862651768504953)
                    ·
                      refine ⟨2800668804646988826378715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734225072862651768504953 2800668804646988826378715)
                      ·
                        rfl

theorem cell23_5454283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 3, 2].length) (baseStart_5454283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454283 prefixEnd_5454283 := by exact prefixLift 5454283
  have htrace : WordTrace (prefixWord ++ tailWord_5454283) baseStart_5454283 baseEnd_5454283 := by
    simpa [prefixWord, tailWord_5454283, baseEnd_5454283] using wordTrace_append hprefix tailTrace_5454283
  have hstable : (prefixWord ++ tailWord_5454283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454283).length < 2 ^ (prefixWord ++ tailWord_5454283).sum := by decide
  have hdescent : baseEnd_5454283 < baseStart_5454283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454286 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_5454286 : Nat := 118140960795 + 5454286 * 2 ^ 59
def prefixEnd_5454286 : Nat := 4983230072969 + 3 ^ 40 * 5454286 * 2
def baseEnd_5454286 : Nat := 2800670345088952314641201

theorem tailTrace_5454286 : CollatzResearch.WordTrace tailWord_5454286 prefixEnd_5454286 2800670345088952314641201 := by
  unfold tailWord_5454286
  simp only [CollatzResearch.WordTrace]
  refine ⟨24866769189757601841497839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132622769012040543154655141 24866769189757601841497839)
  ·
    refine ⟨37300153784636402762246759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24866769189757601841497839 37300153784636402762246759)
    ·
      refine ⟨55950230676954604143370139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37300153784636402762246759 55950230676954604143370139)
      ·
        refine ⟨83925346015431906215055209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55950230676954604143370139 83925346015431906215055209)
        ·
          refine ⟨62944009511573929661291407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83925346015431906215055209 62944009511573929661291407)
          ·
            refine ⟨94416014267360894491937111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62944009511573929661291407 94416014267360894491937111)
            ·
              refine ⟨141624021401041341737905667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94416014267360894491937111 141624021401041341737905667)
              ·
                refine ⟨212436032101562012606858501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141624021401041341737905667 212436032101562012606858501)
                ·
                  refine ⟨39831756019042877363785969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212436032101562012606858501 39831756019042877363785969)
                  ·
                    refine ⟨29873817014282158022839477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39831756019042877363785969 29873817014282158022839477)
                    ·
                      refine ⟨2800670345088952314641201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29873817014282158022839477 2800670345088952314641201)
                      ·
                        rfl

theorem cell23_5454286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_5454286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454286 prefixEnd_5454286 := by exact prefixLift 5454286
  have htrace : WordTrace (prefixWord ++ tailWord_5454286) baseStart_5454286 baseEnd_5454286 := by
    simpa [prefixWord, tailWord_5454286, baseEnd_5454286] using wordTrace_append hprefix tailTrace_5454286
  have hstable : (prefixWord ++ tailWord_5454286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454286).length < 2 ^ (prefixWord ++ tailWord_5454286).sum := by decide
  have hdescent : baseEnd_5454286 < baseStart_5454286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454296 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_5454296 : Nat := 118140960795 + 5454296 * 2 ^ 59
def prefixEnd_5454296 : Nat := 4983230072969 + 3 ^ 40 * 5454296 * 2
def baseEnd_5454296 : Nat := 2800675479895497275516155

theorem tailTrace_5454296 : CollatzResearch.WordTrace tailWord_5454296 prefixEnd_5454296 2800675479895497275516155 := by
  unfold tailWord_5454296
  simp only [CollatzResearch.WordTrace]
  refine ⟨99467259124012293219923371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132623012165349724293231161 99467259124012293219923371)
  ·
    refine ⟨149200888686018439829885057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99467259124012293219923371 149200888686018439829885057)
    ·
      refine ⟨111900666514513829872413793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149200888686018439829885057 111900666514513829872413793)
      ·
        refine ⟨83925499885885372404310345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111900666514513829872413793 83925499885885372404310345)
        ·
          refine ⟨62944124914414029303232759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83925499885885372404310345 62944124914414029303232759)
          ·
            refine ⟨94416187371621043954849139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62944124914414029303232759 94416187371621043954849139)
            ·
              refine ⟨141624281057431565932273709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94416187371621043954849139 141624281057431565932273709)
              ·
                refine ⟨53109105396536837224602641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141624281057431565932273709 53109105396536837224602641)
                ·
                  refine ⟨39831829047402627918451981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53109105396536837224602641 39831829047402627918451981)
                  ·
                    refine ⟨14936935892775985469419493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39831829047402627918451981 14936935892775985469419493)
                    ·
                      refine ⟨2800675479895497275516155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14936935892775985469419493 2800675479895497275516155)
                      ·
                        rfl

theorem cell23_5454296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_5454296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454296 prefixEnd_5454296 := by exact prefixLift 5454296
  have htrace : WordTrace (prefixWord ++ tailWord_5454296) baseStart_5454296 baseEnd_5454296 := by
    simpa [prefixWord, tailWord_5454296, baseEnd_5454296] using wordTrace_append hprefix tailTrace_5454296
  have hstable : (prefixWord ++ tailWord_5454296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454296).length < 2 ^ (prefixWord ++ tailWord_5454296).sum := by decide
  have hdescent : baseEnd_5454296 < baseStart_5454296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454307 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 3]
def baseStart_5454307 : Nat := 118140960795 + 5454307 * 2 ^ 59
def prefixEnd_5454307 : Nat := 4983230072969 + 3 ^ 40 * 5454307 * 2
def baseEnd_5454307 : Nat := 2800681128182696732478605

theorem tailTrace_5454307 : CollatzResearch.WordTrace tailWord_5454307 prefixEnd_5454307 2800681128182696732478605 := by
  unfold tailWord_5454307
  simp only [CollatzResearch.WordTrace]
  refine ⟨198934919450984735318497175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132623279633989823545664783 198934919450984735318497175)
  ·
    refine ⟨298402379176477102977745763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198934919450984735318497175 298402379176477102977745763)
    ·
      refine ⟨447603568764715654466618645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298402379176477102977745763 447603568764715654466618645)
      ·
        refine ⟨20981417285846046303122749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 447603568764715654466618645 20981417285846046303122749)
        ·
          refine ⟨7868031482192267363671031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20981417285846046303122749 7868031482192267363671031)
          ·
            refine ⟨11802047223288401045506547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7868031482192267363671031 11802047223288401045506547)
            ·
              refine ⟨17703070834932601568259821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11802047223288401045506547 17703070834932601568259821)
              ·
                refine ⟨6638651563099725588097433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17703070834932601568259821 6638651563099725588097433)
                ·
                  refine ⟨4978988672324794191073075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6638651563099725588097433 4978988672324794191073075)
                  ·
                    refine ⟨7468483008487191286609613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4978988672324794191073075 7468483008487191286609613)
                    ·
                      refine ⟨2800681128182696732478605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7468483008487191286609613 2800681128182696732478605)
                      ·
                        rfl

theorem cell23_5454307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_5454307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454307 prefixEnd_5454307 := by exact prefixLift 5454307
  have htrace : WordTrace (prefixWord ++ tailWord_5454307) baseStart_5454307 baseEnd_5454307 := by
    simpa [prefixWord, tailWord_5454307, baseEnd_5454307] using wordTrace_append hprefix tailTrace_5454307
  have hstable : (prefixWord ++ tailWord_5454307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454307).length < 2 ^ (prefixWord ++ tailWord_5454307).sum := by decide
  have hdescent : baseEnd_5454307 < baseStart_5454307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454316 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_5454316 : Nat := 118140960795 + 5454316 * 2 ^ 59
def prefixEnd_5454316 : Nat := 4983230072969 + 3 ^ 40 * 5454316 * 2
def baseEnd_5454316 : Nat := 2800685749508587197266063

theorem tailTrace_5454316 : CollatzResearch.WordTrace tailWord_5454316 prefixEnd_5454316 2800685749508587197266063 := by
  unfold tailWord_5454316
  simp only [CollatzResearch.WordTrace]
  refine ⟨99467623853976064927787401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132623498471968086570383201 99467623853976064927787401)
  ·
    refine ⟨74600717890482048695840551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99467623853976064927787401 74600717890482048695840551)
    ·
      refine ⟨111901076835723073043760827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74600717890482048695840551 111901076835723073043760827)
      ·
        refine ⟨167851615253584609565641241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111901076835723073043760827 167851615253584609565641241)
        ·
          refine ⟨125888711440188457174230931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167851615253584609565641241 125888711440188457174230931)
          ·
            refine ⟨188833067160282685761346397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125888711440188457174230931 188833067160282685761346397)
            ·
              refine ⟨70812400185106007160504899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188833067160282685761346397 70812400185106007160504899)
              ·
                refine ⟨106218600277659010740757349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70812400185106007160504899 106218600277659010740757349)
                ·
                  refine ⟨19915987552061064513892003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106218600277659010740757349 19915987552061064513892003)
                  ·
                    refine ⟨29873981328091596770838005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19915987552061064513892003 29873981328091596770838005)
                    ·
                      refine ⟨2800685749508587197266063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29873981328091596770838005 2800685749508587197266063)
                      ·
                        rfl

theorem cell23_5454316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_5454316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454316 prefixEnd_5454316 := by exact prefixLift 5454316
  have htrace : WordTrace (prefixWord ++ tailWord_5454316) baseStart_5454316 baseEnd_5454316 := by
    simpa [prefixWord, tailWord_5454316, baseEnd_5454316] using wordTrace_append hprefix tailTrace_5454316
  have hstable : (prefixWord ++ tailWord_5454316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454316).length < 2 ^ (prefixWord ++ tailWord_5454316).sum := by decide
  have hdescent : baseEnd_5454316 < baseStart_5454316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454317 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5454317 : Nat := 118140960795 + 5454317 * 2 ^ 59
def prefixEnd_5454317 : Nat := 4983230072969 + 3 ^ 40 * 5454317 * 2
def baseEnd_5454317 : Nat := 2800686262989241693353559

theorem tailTrace_5454317 : CollatzResearch.WordTrace tailWord_5454317 prefixEnd_5454317 2800686262989241693353559 := by
  unfold tailWord_5454317
  simp only [CollatzResearch.WordTrace]
  refine ⟨198935284180948507026361205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132623522787299004684240803 198935284180948507026361205)
  ·
    refine ⟨18650182891963922533721363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198935284180948507026361205 18650182891963922533721363)
    ·
      refine ⟨27975274337945883800582045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18650182891963922533721363 27975274337945883800582045)
      ·
        refine ⟨10490727876729706425218267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27975274337945883800582045 10490727876729706425218267)
        ·
          refine ⟨15736091815094559637827401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10490727876729706425218267 15736091815094559637827401)
          ·
            refine ⟨11802068861320919728370551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15736091815094559637827401 11802068861320919728370551)
            ·
              refine ⟨17703103291981379592555827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11802068861320919728370551 17703103291981379592555827)
              ·
                refine ⟨26554654937972069388833741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17703103291981379592555827 26554654937972069388833741)
                ·
                  refine ⟨9957995601739526020812653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26554654937972069388833741 9957995601739526020812653)
                  ·
                    refine ⟨3734248350652322257804745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9957995601739526020812653 3734248350652322257804745)
                    ·
                      refine ⟨2800686262989241693353559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734248350652322257804745 2800686262989241693353559)
                      ·
                        rfl

theorem cell23_5454317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5454317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454317 prefixEnd_5454317 := by exact prefixLift 5454317
  have htrace : WordTrace (prefixWord ++ tailWord_5454317) baseStart_5454317 baseEnd_5454317 := by
    simpa [prefixWord, tailWord_5454317, baseEnd_5454317] using wordTrace_append hprefix tailTrace_5454317
  have hstable : (prefixWord ++ tailWord_5454317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454317).length < 2 ^ (prefixWord ++ tailWord_5454317).sum := by decide
  have hdescent : baseEnd_5454317 < baseStart_5454317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454330 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2]
def baseStart_5454330 : Nat := 118140960795 + 5454330 * 2 ^ 59
def prefixEnd_5454330 : Nat := 4983230072969 + 3 ^ 40 * 5454330 * 2
def baseEnd_5454330 : Nat := 2800692938237750142490999

theorem tailTrace_5454330 : CollatzResearch.WordTrace tailWord_5454330 prefixEnd_5454330 2800692938237750142490999 := by
  unfold tailWord_5454330
  simp only [CollatzResearch.WordTrace]
  refine ⟨49733939582475352561646111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132623838886600940164389629 49733939582475352561646111)
  ·
    refine ⟨74600909373713028842469167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49733939582475352561646111 74600909373713028842469167)
    ·
      refine ⟨111901364060569543263703751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74600909373713028842469167 111901364060569543263703751)
      ·
        refine ⟨167852046090854314895555627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111901364060569543263703751 167852046090854314895555627)
        ·
          refine ⟨251778069136281472343333441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167852046090854314895555627 251778069136281472343333441)
          ·
            refine ⟨188833551852211104257500081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251778069136281472343333441 188833551852211104257500081)
            ·
              refine ⟨141625163889158328193125061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188833551852211104257500081 141625163889158328193125061)
              ·
                refine ⟨26554718229217186536210949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141625163889158328193125061 26554718229217186536210949)
                ·
                  refine ⟨4979009667978222475539553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26554718229217186536210949 4979009667978222475539553)
                  ·
                    refine ⟨3734257250983666856654665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4979009667978222475539553 3734257250983666856654665)
                    ·
                      refine ⟨2800692938237750142490999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734257250983666856654665 2800692938237750142490999)
                      ·
                        rfl

theorem cell23_5454330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_5454330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454330 prefixEnd_5454330 := by exact prefixLift 5454330
  have htrace : WordTrace (prefixWord ++ tailWord_5454330) baseStart_5454330 baseEnd_5454330 := by
    simpa [prefixWord, tailWord_5454330, baseEnd_5454330] using wordTrace_append hprefix tailTrace_5454330
  have hstable : (prefixWord ++ tailWord_5454330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454330).length < 2 ^ (prefixWord ++ tailWord_5454330).sum := by decide
  have hdescent : baseEnd_5454330 < baseStart_5454330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454342 : List Nat := [6, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_5454342 : Nat := 118140960795 + 5454342 * 2 ^ 59
def prefixEnd_5454342 : Nat := 4983230072969 + 3 ^ 40 * 5454342 * 2
def baseEnd_5454342 : Nat := 2800699100005604095540945

theorem tailTrace_5454342 : CollatzResearch.WordTrace tailWord_5454342 prefixEnd_5454342 2800699100005604095540945 := by
  unfold tailWord_5454342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6216756125183060509250665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132624130670571957530680853 6216756125183060509250665)
  ·
    refine ⟨4662567093887295381937999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6216756125183060509250665 4662567093887295381937999)
    ·
      refine ⟨6993850640830943072906999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4662567093887295381937999 6993850640830943072906999)
      ·
        refine ⟨10490775961246414609360499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993850640830943072906999 10490775961246414609360499)
        ·
          refine ⟨15736163941869621914040749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10490775961246414609360499 15736163941869621914040749)
          ·
            refine ⟨5901061478201108217765281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15736163941869621914040749 5901061478201108217765281)
            ·
              refine ⟨4425796108650831163323961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5901061478201108217765281 4425796108650831163323961)
              ·
                refine ⟨3319347081488123372492971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4425796108650831163323961 3319347081488123372492971)
                ·
                  refine ⟨4979020622232185058739457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319347081488123372492971 4979020622232185058739457)
                  ·
                    refine ⟨3734265466674138794054593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4979020622232185058739457 3734265466674138794054593)
                    ·
                      refine ⟨2800699100005604095540945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734265466674138794054593 2800699100005604095540945)
                      ·
                        rfl

theorem cell23_5454342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_5454342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454342 prefixEnd_5454342 := by exact prefixLift 5454342
  have htrace : WordTrace (prefixWord ++ tailWord_5454342) baseStart_5454342 baseEnd_5454342 := by
    simpa [prefixWord, tailWord_5454342, baseEnd_5454342] using wordTrace_append hprefix tailTrace_5454342
  have hstable : (prefixWord ++ tailWord_5454342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454342).length < 2 ^ (prefixWord ++ tailWord_5454342).sum := by decide
  have hdescent : baseEnd_5454342 < baseStart_5454342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454347 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 2, 2, 2]
def baseStart_5454347 : Nat := 118140960795 + 5454347 * 2 ^ 59
def prefixEnd_5454347 : Nat := 4983230072969 + 3 ^ 40 * 5454347 * 2
def baseEnd_5454347 : Nat := 2800701667408876575978421

theorem tailTrace_5454347 : CollatzResearch.WordTrace tailWord_5454347 prefixEnd_5454347 2800701667408876575978421 := by
  unfold tailWord_5454347
  simp only [CollatzResearch.WordTrace]
  refine ⟨198936378370839822149953295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132624252247226548099968863 198936378370839822149953295)
  ·
    refine ⟨298404567556259733224929943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198936378370839822149953295 298404567556259733224929943)
    ·
      refine ⟨447606851334389599837394915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298404567556259733224929943 447606851334389599837394915)
      ·
        refine ⟨671410277001584399756092373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447606851334389599837394915 671410277001584399756092373)
        ·
          refine ⟨15736178367224634369283415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 671410277001584399756092373 15736178367224634369283415)
          ·
            refine ⟨23604267550836951553925123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15736178367224634369283415 23604267550836951553925123)
            ·
              refine ⟨35406401326255427330887685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23604267550836951553925123 35406401326255427330887685)
              ·
                refine ⟨6638700248672892624541441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35406401326255427330887685 6638700248672892624541441)
                ·
                  refine ⟨4979025186504669468406081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6638700248672892624541441 4979025186504669468406081)
                  ·
                    refine ⟨3734268889878502101304561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4979025186504669468406081 3734268889878502101304561)
                    ·
                      refine ⟨2800701667408876575978421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734268889878502101304561 2800701667408876575978421)
                      ·
                        rfl

theorem cell23_5454347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 2, 2].length) (baseStart_5454347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454347 prefixEnd_5454347 := by exact prefixLift 5454347
  have htrace : WordTrace (prefixWord ++ tailWord_5454347) baseStart_5454347 baseEnd_5454347 := by
    simpa [prefixWord, tailWord_5454347, baseEnd_5454347] using wordTrace_append hprefix tailTrace_5454347
  have hstable : (prefixWord ++ tailWord_5454347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454347).length < 2 ^ (prefixWord ++ tailWord_5454347).sum := by decide
  have hdescent : baseEnd_5454347 < baseStart_5454347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454398 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5454398 : Nat := 118140960795 + 5454398 * 2 ^ 59
def prefixEnd_5454398 : Nat := 4983230072969 + 3 ^ 40 * 5454398 * 2
def baseEnd_5454398 : Nat := 2800727854922255876440687

theorem tailTrace_5454398 : CollatzResearch.WordTrace tailWord_5454398 prefixEnd_5454398 2800727854922255876440687 := by
  unfold tailWord_5454398
  simp only [CollatzResearch.WordTrace]
  refine ⟨24867279811706882232507481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132625492329103371906706565 24867279811706882232507481)
  ·
    refine ⟨18650459858780161674380611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24867279811706882232507481 18650459858780161674380611)
    ·
      refine ⟨27975689788170242511570917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18650459858780161674380611 27975689788170242511570917)
      ·
        refine ⟨5245441835281920470919547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27975689788170242511570917 5245441835281920470919547)
        ·
          refine ⟨7868162752922880706379321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245441835281920470919547 7868162752922880706379321)
          ·
            refine ⟨5901122064692160529784491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7868162752922880706379321 5901122064692160529784491)
            ·
              refine ⟨8851683097038240794676737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901122064692160529784491 8851683097038240794676737)
              ·
                refine ⟨6638762322778680596007553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8851683097038240794676737 6638762322778680596007553)
                ·
                  refine ⟨4979071742084010447005665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6638762322778680596007553 4979071742084010447005665)
                  ·
                    refine ⟨3734303806563007835254249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4979071742084010447005665 3734303806563007835254249)
                    ·
                      refine ⟨2800727854922255876440687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734303806563007835254249 2800727854922255876440687)
                      ·
                        rfl

theorem cell23_5454398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5454398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454398 prefixEnd_5454398 := by exact prefixLift 5454398
  have htrace : WordTrace (prefixWord ++ tailWord_5454398) baseStart_5454398 baseEnd_5454398 := by
    simpa [prefixWord, tailWord_5454398, baseEnd_5454398] using wordTrace_append hprefix tailTrace_5454398
  have hstable : (prefixWord ++ tailWord_5454398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454398).length < 2 ^ (prefixWord ++ tailWord_5454398).sum := by decide
  have hdescent : baseEnd_5454398 < baseStart_5454398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454403 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 4]
def baseStart_5454403 : Nat := 118140960795 + 5454403 * 2 ^ 59
def prefixEnd_5454403 : Nat := 4983230072969 + 3 ^ 40 * 5454403 * 2
def baseEnd_5454403 : Nat := 2800730422325528356878163

theorem tailTrace_5454403 : CollatzResearch.WordTrace tailWord_5454403 prefixEnd_5454403 2800730422325528356878163 := by
  unfold tailWord_5454403
  simp only [CollatzResearch.WordTrace]
  refine ⟨198938420858636943713991863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132625613905757962475994575 198938420858636943713991863)
  ·
    refine ⟨298407631287955415570987795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198938420858636943713991863 298407631287955415570987795)
    ·
      refine ⟨447611446931933123356481693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298407631287955415570987795 447611446931933123356481693)
      ·
        refine ⟨167854292599474921258680635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447611446931933123356481693 167854292599474921258680635)
        ·
          refine ⟨251781438899212381888020953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167854292599474921258680635 251781438899212381888020953)
          ·
            refine ⟨188836079174409286416015715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251781438899212381888020953 188836079174409286416015715)
            ·
              refine ⟨283254118761613929624023573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188836079174409286416015715 283254118761613929624023573)
              ·
                refine ⟨13277536816950652951126105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 283254118761613929624023573 13277536816950652951126105)
                ·
                  refine ⟨9958152612712989713344579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13277536816950652951126105 9958152612712989713344579)
                  ·
                    refine ⟨14937228919069484570016869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9958152612712989713344579 14937228919069484570016869)
                    ·
                      refine ⟨2800730422325528356878163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14937228919069484570016869 2800730422325528356878163)
                      ·
                        rfl

theorem cell23_5454403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_5454403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454403 prefixEnd_5454403 := by exact prefixLift 5454403
  have htrace : WordTrace (prefixWord ++ tailWord_5454403) baseStart_5454403 baseEnd_5454403 := by
    simpa [prefixWord, tailWord_5454403, baseEnd_5454403] using wordTrace_append hprefix tailTrace_5454403
  have hstable : (prefixWord ++ tailWord_5454403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454403).length < 2 ^ (prefixWord ++ tailWord_5454403).sum := by decide
  have hdescent : baseEnd_5454403 < baseStart_5454403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454404 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 7]
def baseStart_5454404 : Nat := 118140960795 + 5454404 * 2 ^ 59
def prefixEnd_5454404 : Nat := 4983230072969 + 3 ^ 40 * 5454404 * 2
def baseEnd_5454404 : Nat := 311192326200686983662851

theorem tailTrace_5454404 : CollatzResearch.WordTrace tailWord_5454404 prefixEnd_5454404 311192326200686983662851 := by
  unfold tailWord_5454404
  simp only [CollatzResearch.WordTrace]
  refine ⟨99469228665816660442389133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132625638221088880589852177 99469228665816660442389133)
  ·
    refine ⟨37300960749681247665895925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99469228665816660442389133 37300960749681247665895925)
    ·
      refine ⟨3496965070282616968677743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37300960749681247665895925 3496965070282616968677743)
      ·
        refine ⟨5245447605423925453016615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3496965070282616968677743 5245447605423925453016615)
        ·
          refine ⟨7868171408135888179524923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245447605423925453016615 7868171408135888179524923)
          ·
            refine ⟨11802257112203832269287385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7868171408135888179524923 11802257112203832269287385)
            ·
              refine ⟨8851692834152874201965539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11802257112203832269287385 8851692834152874201965539)
              ·
                refine ⟨13277539251229311302948309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8851692834152874201965539 13277539251229311302948309)
                ·
                  refine ⟨311192326200686983662851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13277539251229311302948309 311192326200686983662851)
                  ·
                    rfl

theorem cell23_5454404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_5454404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454404 prefixEnd_5454404 := by exact prefixLift 5454404
  have htrace : WordTrace (prefixWord ++ tailWord_5454404) baseStart_5454404 baseEnd_5454404 := by
    simpa [prefixWord, tailWord_5454404, baseEnd_5454404] using wordTrace_append hprefix tailTrace_5454404
  have hstable : (prefixWord ++ tailWord_5454404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454404).length < 2 ^ (prefixWord ++ tailWord_5454404).sum := by decide
  have hdescent : baseEnd_5454404 < baseStart_5454404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454423 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_5454423 : Nat := 118140960795 + 5454423 * 2 ^ 59
def prefixEnd_5454423 : Nat := 4983230072969 + 3 ^ 40 * 5454423 * 2
def baseEnd_5454423 : Nat := 2800740691938618278628071

theorem tailTrace_5454423 : CollatzResearch.WordTrace tailWord_5454423 prefixEnd_5454423 2800740691938618278628071 := by
  unfold tailWord_5454423
  simp only [CollatzResearch.WordTrace]
  refine ⟨198939150318564487129719923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132626100212376324753146615 198939150318564487129719923)
  ·
    refine ⟨298408725477846730694579885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198939150318564487129719923 298408725477846730694579885)
    ·
      refine ⟨111903272054192524010467457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298408725477846730694579885 111903272054192524010467457)
      ·
        refine ⟨83927454040644393007850593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111903272054192524010467457 83927454040644393007850593)
        ·
          refine ⟨62945590530483294755887945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83927454040644393007850593 62945590530483294755887945)
          ·
            refine ⟨47209192897862471066915959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62945590530483294755887945 47209192897862471066915959)
            ·
              refine ⟨70813789346793706600373939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47209192897862471066915959 70813789346793706600373939)
              ·
                refine ⟨106220684020190559900560909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70813789346793706600373939 106220684020190559900560909)
                ·
                  refine ⟨39832756507571459962710341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106220684020190559900560909 39832756507571459962710341)
                  ·
                    refine ⟨7468641845169648743008189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39832756507571459962710341 7468641845169648743008189)
                    ·
                      refine ⟨2800740691938618278628071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7468641845169648743008189 2800740691938618278628071)
                      ·
                        rfl

theorem cell23_5454423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_5454423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454423 prefixEnd_5454423 := by exact prefixLift 5454423
  have htrace : WordTrace (prefixWord ++ tailWord_5454423) baseStart_5454423 baseEnd_5454423 := by
    simpa [prefixWord, tailWord_5454423, baseEnd_5454423] using wordTrace_append hprefix tailTrace_5454423
  have hstable : (prefixWord ++ tailWord_5454423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454423).length < 2 ^ (prefixWord ++ tailWord_5454423).sum := by decide
  have hdescent : baseEnd_5454423 < baseStart_5454423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454447 : List Nat := [1, 1, 2, 1, 3, 2, 5, 3, 1, 4]
def baseStart_5454447 : Nat := 118140960795 + 5454447 * 2 ^ 59
def prefixEnd_5454447 : Nat := 4983230072969 + 3 ^ 40 * 5454447 * 2
def baseEnd_5454447 : Nat := 933584338491442061575987

theorem tailTrace_5454447 : CollatzResearch.WordTrace tailWord_5454447 prefixEnd_5454447 933584338491442061575987 := by
  unfold tailWord_5454447
  simp only [CollatzResearch.WordTrace]
  refine ⟨198940025670477539228593595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132626683780318359485729063 198940025670477539228593595)
  ·
    refine ⟨298410038505716308842890393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198940025670477539228593595 298410038505716308842890393)
    ·
      refine ⟨223807528879287231632167795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298410038505716308842890393 223807528879287231632167795)
      ·
        refine ⟨335711293318930847448251693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223807528879287231632167795 335711293318930847448251693)
        ·
          refine ⟨125891734994599067793094385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335711293318930847448251693 125891734994599067793094385)
          ·
            refine ⟨94418801245949300844820789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125891734994599067793094385 94418801245949300844820789)
            ·
              refine ⟨8851762616807746954201949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94418801245949300844820789 8851762616807746954201949)
              ·
                refine ⟨3319410981302905107825731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8851762616807746954201949 3319410981302905107825731)
                ·
                  refine ⟨4979116471954357661738597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319410981302905107825731 4979116471954357661738597)
                  ·
                    refine ⟨933584338491442061575987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4979116471954357661738597 933584338491442061575987)
                    ·
                      rfl

theorem cell23_5454447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 4].length) (baseStart_5454447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454447 prefixEnd_5454447 := by exact prefixLift 5454447
  have htrace : WordTrace (prefixWord ++ tailWord_5454447) baseStart_5454447 baseEnd_5454447 := by
    simpa [prefixWord, tailWord_5454447, baseEnd_5454447] using wordTrace_append hprefix tailTrace_5454447
  have hstable : (prefixWord ++ tailWord_5454447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454447).length < 2 ^ (prefixWord ++ tailWord_5454447).sum := by decide
  have hdescent : baseEnd_5454447 < baseStart_5454447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454464 : List Nat := [2, 1, 1, 2, 1, 6, 3, 2, 1, 4]
def baseStart_5454464 : Nat := 118140960795 + 5454464 * 2 ^ 59
def prefixEnd_5454464 : Nat := 4983230072969 + 3 ^ 40 * 5454464 * 2
def baseEnd_5454464 : Nat := 933587248215150872738461

theorem tailTrace_5454464 : CollatzResearch.WordTrace tailWord_5454464 prefixEnd_5454464 933587248215150872738461 := by
  unfold tailWord_5454464
  simp only [CollatzResearch.WordTrace]
  refine ⟨99470322855707975565981223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132627097140943967421308297 99470322855707975565981223)
  ·
    refine ⟨149205484283561963348971835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99470322855707975565981223 149205484283561963348971835)
    ·
      refine ⟨223808226425342945023457753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149205484283561963348971835 223808226425342945023457753)
      ·
        refine ⟨167856169819007208767593315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223808226425342945023457753 167856169819007208767593315)
        ·
          refine ⟨251784254728510813151389973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167856169819007208767593315 251784254728510813151389973)
          ·
            refine ⟨11802386940398944366471405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 251784254728510813151389973 11802386940398944366471405)
            ·
              refine ⟨4425895102649604137426777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11802386940398944366471405 4425895102649604137426777)
              ·
                refine ⟨3319421326987203103070083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4425895102649604137426777 3319421326987203103070083)
                ·
                  refine ⟨4979131990480804654605125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319421326987203103070083 4979131990480804654605125)
                  ·
                    refine ⟨933587248215150872738461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4979131990480804654605125 933587248215150872738461)
                    ·
                      rfl

theorem cell23_5454464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 4].length) (baseStart_5454464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454464 prefixEnd_5454464 := by exact prefixLift 5454464
  have htrace : WordTrace (prefixWord ++ tailWord_5454464) baseStart_5454464 baseEnd_5454464 := by
    simpa [prefixWord, tailWord_5454464, baseEnd_5454464] using wordTrace_append hprefix tailTrace_5454464
  have hstable : (prefixWord ++ tailWord_5454464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454464).length < 2 ^ (prefixWord ++ tailWord_5454464).sum := by decide
  have hdescent : baseEnd_5454464 < baseStart_5454464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454473 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 3, 5]
def baseStart_5454473 : Nat := 118140960795 + 5454473 * 2 ^ 59
def prefixEnd_5454473 : Nat := 4983230072969 + 3 ^ 40 * 5454473 * 2
def baseEnd_5454473 : Nat := 933588788657114361000947

theorem tailTrace_5454473 : CollatzResearch.WordTrace tailWord_5454473 prefixEnd_5454473 933588788657114361000947 := by
  unfold tailWord_5454473
  simp only [CollatzResearch.WordTrace]
  refine ⟨198940973968383345669040073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132627315978922230446026715 198940973968383345669040073)
  ·
    refine ⟨149205730476287509251780055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198940973968383345669040073 149205730476287509251780055)
    ·
      refine ⟨223808595714431263877670083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149205730476287509251780055 223808595714431263877670083)
      ·
        refine ⟨335712893571646895816505125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223808595714431263877670083 335712893571646895816505125)
        ·
          refine ⟨62946167544683792965594711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335712893571646895816505125 62946167544683792965594711)
          ·
            refine ⟨94419251317025689448392067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62946167544683792965594711 94419251317025689448392067)
            ·
              refine ⟨141628876975538534172588101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94419251317025689448392067 141628876975538534172588101)
              ·
                refine ⟨26555414432913475157360269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141628876975538534172588101 26555414432913475157360269)
                ·
                  refine ⟨9958280412342553184010101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26555414432913475157360269 9958280412342553184010101)
                  ·
                    refine ⟨933588788657114361000947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9958280412342553184010101 933588788657114361000947)
                    ·
                      rfl

theorem cell23_5454473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_5454473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454473 prefixEnd_5454473 := by exact prefixLift 5454473
  have htrace : WordTrace (prefixWord ++ tailWord_5454473) baseStart_5454473 baseEnd_5454473 := by
    simpa [prefixWord, tailWord_5454473, baseEnd_5454473] using wordTrace_append hprefix tailTrace_5454473
  have hstable : (prefixWord ++ tailWord_5454473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454473).length < 2 ^ (prefixWord ++ tailWord_5454473).sum := by decide
  have hdescent : baseEnd_5454473 < baseStart_5454473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454548 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5454548 : Nat := 118140960795 + 5454548 * 2 ^ 59
def prefixEnd_5454548 : Nat := 4983230072969 + 3 ^ 40 * 5454548 * 2
def baseEnd_5454548 : Nat := 2800804877020430289564997

theorem tailTrace_5454548 : CollatzResearch.WordTrace tailWord_5454548 prefixEnd_5454548 2800804877020430289564997 := by
  unfold tailWord_5454548
  simp only [CollatzResearch.WordTrace]
  refine ⟨99471854721555816739010149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132629139628741088985346865 99471854721555816739010149)
  ·
    refine ⟨18650972760291715638564403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99471854721555816739010149 18650972760291715638564403)
    ·
      refine ⟨27976459140437573457846605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18650972760291715638564403 27976459140437573457846605)
      ·
        refine ⟨10491172177664090046692477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27976459140437573457846605 10491172177664090046692477)
        ·
          refine ⟨3934189566624033767509679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10491172177664090046692477 3934189566624033767509679)
          ·
            refine ⟨5901284349936050651264519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934189566624033767509679 5901284349936050651264519)
            ·
              refine ⟨8851926524904075976896779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901284349936050651264519 8851926524904075976896779)
              ·
                refine ⟨13277889787356113965345169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8851926524904075976896779 13277889787356113965345169)
                ·
                  refine ⟨9958417340517085474008877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13277889787356113965345169 9958417340517085474008877)
                  ·
                    refine ⟨3734406502693907052753329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9958417340517085474008877 3734406502693907052753329)
                    ·
                      refine ⟨2800804877020430289564997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734406502693907052753329 2800804877020430289564997)
                      ·
                        rfl

theorem cell23_5454548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5454548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454548 prefixEnd_5454548 := by exact prefixLift 5454548
  have htrace : WordTrace (prefixWord ++ tailWord_5454548) baseStart_5454548 baseEnd_5454548 := by
    simpa [prefixWord, tailWord_5454548, baseEnd_5454548] using wordTrace_append hprefix tailTrace_5454548
  have hstable : (prefixWord ++ tailWord_5454548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454548).length < 2 ^ (prefixWord ++ tailWord_5454548).sum := by decide
  have hdescent : baseEnd_5454548 < baseStart_5454548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454561 : List Nat := [1, 2, 3, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_5454561 : Nat := 118140960795 + 5454561 * 2 ^ 59
def prefixEnd_5454561 : Nat := 4983230072969 + 3 ^ 40 * 5454561 * 2
def baseEnd_5454561 : Nat := 2800811552268938738702437

theorem tailTrace_5454561 : CollatzResearch.WordTrace tailWord_5454561 prefixEnd_5454561 2800811552268938738702437 := by
  unfold tailWord_5454561
  simp only [CollatzResearch.WordTrace]
  refine ⟨198944183592064536698243537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132629455728043024465495691 198944183592064536698243537)
  ·
    refine ⟨149208137694048402523682653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198944183592064536698243537 149208137694048402523682653)
    ·
      refine ⟨55953051635268150946380995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149208137694048402523682653 55953051635268150946380995)
      ·
        refine ⟨83929577452902226419571493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55953051635268150946380995 83929577452902226419571493)
        ·
          refine ⟨15736795772419167453669655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83929577452902226419571493 15736795772419167453669655)
          ·
            refine ⟨23605193658628751180504483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15736795772419167453669655 23605193658628751180504483)
            ·
              refine ⟨35407790487943126770756725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23605193658628751180504483 35407790487943126770756725)
              ·
                refine ⟨3319480358244668134758443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35407790487943126770756725 3319480358244668134758443)
                ·
                  refine ⟨4979220537367002202137665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319480358244668134758443 4979220537367002202137665)
                  ·
                    refine ⟨3734415403025251651603249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4979220537367002202137665 3734415403025251651603249)
                    ·
                      refine ⟨2800811552268938738702437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734415403025251651603249 2800811552268938738702437)
                      ·
                        rfl

theorem cell23_5454561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_5454561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454561 prefixEnd_5454561 := by exact prefixLift 5454561
  have htrace : WordTrace (prefixWord ++ tailWord_5454561) baseStart_5454561 baseEnd_5454561 := by
    simpa [prefixWord, tailWord_5454561, baseEnd_5454561] using wordTrace_append hprefix tailTrace_5454561
  have hstable : (prefixWord ++ tailWord_5454561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454561).length < 2 ^ (prefixWord ++ tailWord_5454561).sum := by decide
  have hdescent : baseEnd_5454561 < baseStart_5454561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454564 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_5454564 : Nat := 118140960795 + 5454564 * 2 ^ 59
def prefixEnd_5454564 : Nat := 4983230072969 + 3 ^ 40 * 5454564 * 2
def baseEnd_5454564 : Nat := 2800813092710902226964923

theorem tailTrace_5454564 : CollatzResearch.WordTrace tailWord_5454564 prefixEnd_5454564 2800813092710902226964923 := by
  unfold tailWord_5454564
  simp only [CollatzResearch.WordTrace]
  refine ⟨99472146505526834105301373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132629528674035778807068497 99472146505526834105301373)
  ·
    refine ⟨37302054939572562789488015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99472146505526834105301373 37302054939572562789488015)
    ·
      refine ⟨55953082409358844184232023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37302054939572562789488015 55953082409358844184232023)
      ·
        refine ⟨83929623614038266276348035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55953082409358844184232023 83929623614038266276348035)
        ·
          refine ⟨125894435421057399414522053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83929623614038266276348035 125894435421057399414522053)
          ·
            refine ⟨23605206641448262390222885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125894435421057399414522053 23605206641448262390222885)
            ·
              refine ⟨4425976245271549198166791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23605206641448262390222885 4425976245271549198166791)
              ·
                refine ⟨6638964367907323797250187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425976245271549198166791 6638964367907323797250187)
                ·
                  refine ⟨9958446551860985695875281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6638964367907323797250187 9958446551860985695875281)
                  ·
                    refine ⟨7468834913895739271906461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9958446551860985695875281 7468834913895739271906461)
                    ·
                      refine ⟨2800813092710902226964923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7468834913895739271906461 2800813092710902226964923)
                      ·
                        rfl

theorem cell23_5454564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_5454564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454564 prefixEnd_5454564 := by exact prefixLift 5454564
  have htrace : WordTrace (prefixWord ++ tailWord_5454564) baseStart_5454564 baseEnd_5454564 := by
    simpa [prefixWord, tailWord_5454564, baseEnd_5454564] using wordTrace_append hprefix tailTrace_5454564
  have hstable : (prefixWord ++ tailWord_5454564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454564).length < 2 ^ (prefixWord ++ tailWord_5454564).sum := by decide
  have hdescent : baseEnd_5454564 < baseStart_5454564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454577 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_5454577 : Nat := 118140960795 + 5454577 * 2 ^ 59
def prefixEnd_5454577 : Nat := 4983230072969 + 3 ^ 40 * 5454577 * 2
def baseEnd_5454577 : Nat := 2800819767959410676102363

theorem tailTrace_5454577 : CollatzResearch.WordTrace tailWord_5454577 prefixEnd_5454577 2800819767959410676102363 := by
  unfold tailWord_5454577
  simp only [CollatzResearch.WordTrace]
  refine ⟨198944767160006571430825985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132629844773337714287217323 198944767160006571430825985)
  ·
    refine ⟨149208575370004928573119489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198944767160006571430825985 149208575370004928573119489)
    ·
      refine ⟨111906431527503696429839617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149208575370004928573119489 111906431527503696429839617)
      ·
        refine ⟨83929823645627772322379713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111906431527503696429839617 83929823645627772322379713)
        ·
          refine ⟨62947367734220829241784785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83929823645627772322379713 62947367734220829241784785)
          ·
            refine ⟨47210525800665621931338589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62947367734220829241784785 47210525800665621931338589)
            ·
              refine ⟨17703947175249608224251971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47210525800665621931338589 17703947175249608224251971)
              ·
                refine ⟨26555920762874412336377957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17703947175249608224251971 26555920762874412336377957)
                ·
                  refine ⟨4979235143038952313070867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26555920762874412336377957 4979235143038952313070867)
                  ·
                    refine ⟨7468852714558428469606301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4979235143038952313070867 7468852714558428469606301)
                    ·
                      refine ⟨2800819767959410676102363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7468852714558428469606301 2800819767959410676102363)
                      ·
                        rfl

theorem cell23_5454577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_5454577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454577 prefixEnd_5454577 := by exact prefixLift 5454577
  have htrace : WordTrace (prefixWord ++ tailWord_5454577) baseStart_5454577 baseEnd_5454577 := by
    simpa [prefixWord, tailWord_5454577, baseEnd_5454577] using wordTrace_append hprefix tailTrace_5454577
  have hstable : (prefixWord ++ tailWord_5454577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454577).length < 2 ^ (prefixWord ++ tailWord_5454577).sum := by decide
  have hdescent : baseEnd_5454577 < baseStart_5454577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454581 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5454581 : Nat := 118140960795 + 5454581 * 2 ^ 59
def prefixEnd_5454581 : Nat := 4983230072969 + 3 ^ 40 * 5454581 * 2
def baseEnd_5454581 : Nat := 2800821821882028660452345

theorem tailTrace_5454581 : CollatzResearch.WordTrace tailWord_5454581 prefixEnd_5454581 2800821821882028660452345 := by
  unfold tailWord_5454581
  simp only [CollatzResearch.WordTrace]
  refine ⟨198944913051992080113971597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132629942034661386742647731 198944913051992080113971597)
  ·
    refine ⟨74604342394497030042739349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198944913051992080113971597 74604342394497030042739349)
    ·
      refine ⟨3497078549742048283253407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74604342394497030042739349 3497078549742048283253407)
      ·
        refine ⟨5245617824613072424880111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497078549742048283253407 5245617824613072424880111)
        ·
          refine ⟨7868426736919608637320167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245617824613072424880111 7868426736919608637320167)
          ·
            refine ⟨11802640105379412955980251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7868426736919608637320167 11802640105379412955980251)
            ·
              refine ⟨17703960158069119433970377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11802640105379412955980251 17703960158069119433970377)
              ·
                refine ⟨13277970118551839575477783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17703960158069119433970377 13277970118551839575477783)
                ·
                  refine ⟨19916955177827759363216675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13277970118551839575477783 19916955177827759363216675)
                  ·
                    refine ⟨29875432766741639044825013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19916955177827759363216675 29875432766741639044825013)
                    ·
                      refine ⟨2800821821882028660452345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29875432766741639044825013 2800821821882028660452345)
                      ·
                        rfl

theorem cell23_5454581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5454581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454581 prefixEnd_5454581 := by exact prefixLift 5454581
  have htrace : WordTrace (prefixWord ++ tailWord_5454581) baseStart_5454581 baseEnd_5454581 := by
    simpa [prefixWord, tailWord_5454581, baseEnd_5454581] using wordTrace_append hprefix tailTrace_5454581
  have hstable : (prefixWord ++ tailWord_5454581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454581).length < 2 ^ (prefixWord ++ tailWord_5454581).sum := by decide
  have hdescent : baseEnd_5454581 < baseStart_5454581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454594 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_5454594 : Nat := 118140960795 + 5454594 * 2 ^ 59
def prefixEnd_5454594 : Nat := 4983230072969 + 3 ^ 40 * 5454594 * 2
def baseEnd_5454594 : Nat := 2800828497130537109589785

theorem tailTrace_5454594 : CollatzResearch.WordTrace tailWord_5454594 prefixEnd_5454594 2800828497130537109589785 := by
  unfold tailWord_5454594
  simp only [CollatzResearch.WordTrace]
  refine ⟨49736346800236245833548709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132630258133963322222796557 49736346800236245833548709)
  ·
    refine ⟨9325565025044296093790383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49736346800236245833548709 9325565025044296093790383)
    ·
      refine ⟨13988347537566444140685575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9325565025044296093790383 13988347537566444140685575)
      ·
        refine ⟨20982521306349666211028363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13988347537566444140685575 20982521306349666211028363)
        ·
          refine ⟨31473781959524499316542545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20982521306349666211028363 31473781959524499316542545)
          ·
            refine ⟨23605336469643374487406909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31473781959524499316542545 23605336469643374487406909)
            ·
              refine ⟨8852001176116265432777591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23605336469643374487406909 8852001176116265432777591)
              ·
                refine ⟨13278001764174398149166387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8852001176116265432777591 13278001764174398149166387)
                ·
                  refine ⟨19917002646261597223749581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13278001764174398149166387 19917002646261597223749581)
                  ·
                    refine ⟨7468875992348098958906093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19917002646261597223749581 7468875992348098958906093)
                    ·
                      refine ⟨2800828497130537109589785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7468875992348098958906093 2800828497130537109589785)
                      ·
                        rfl

theorem cell23_5454594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_5454594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454594 prefixEnd_5454594 := by exact prefixLift 5454594
  have htrace : WordTrace (prefixWord ++ tailWord_5454594) baseStart_5454594 baseEnd_5454594 := by
    simpa [prefixWord, tailWord_5454594, baseEnd_5454594] using wordTrace_append hprefix tailTrace_5454594
  have hstable : (prefixWord ++ tailWord_5454594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454594).length < 2 ^ (prefixWord ++ tailWord_5454594).sum := by decide
  have hdescent : baseEnd_5454594 < baseStart_5454594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454620 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_5454620 : Nat := 118140960795 + 5454620 * 2 ^ 59
def prefixEnd_5454620 : Nat := 4983230072969 + 3 ^ 40 * 5454620 * 2
def baseEnd_5454620 : Nat := 2800841847627554007864665

theorem tailTrace_5454620 : CollatzResearch.WordTrace tailWord_5454620 prefixEnd_5454620 2800841847627554007864665 := by
  unfold tailWord_5454620
  simp only [CollatzResearch.WordTrace]
  refine ⟨99473167749425394887320657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132630890332567193183094209 99473167749425394887320657)
  ·
    refine ⟨74604875812069046165490493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99473167749425394887320657 74604875812069046165490493)
    ·
      refine ⟨27976828429525892312058935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74604875812069046165490493 27976828429525892312058935)
      ·
        refine ⟨41965242644288838468088403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27976828429525892312058935 41965242644288838468088403)
        ·
          refine ⟨62947863966433257702132605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41965242644288838468088403 62947863966433257702132605)
          ·
            refine ⟨23605448987412471638299727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62947863966433257702132605 23605448987412471638299727)
            ·
              refine ⟨35408173481118707457449591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23605448987412471638299727 35408173481118707457449591)
              ·
                refine ⟨53112260221678061186174387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35408173481118707457449591 53112260221678061186174387)
                ·
                  refine ⟨79668390332517091779261581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53112260221678061186174387 79668390332517091779261581)
                  ·
                    refine ⟨29875646374693909417223093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79668390332517091779261581 29875646374693909417223093)
                    ·
                      refine ⟨2800841847627554007864665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29875646374693909417223093 2800841847627554007864665)
                      ·
                        rfl

theorem cell23_5454620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_5454620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454620 prefixEnd_5454620 := by exact prefixLift 5454620
  have htrace : WordTrace (prefixWord ++ tailWord_5454620) baseStart_5454620 baseEnd_5454620 := by
    simpa [prefixWord, tailWord_5454620, baseEnd_5454620] using wordTrace_append hprefix tailTrace_5454620
  have hstable : (prefixWord ++ tailWord_5454620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454620).length < 2 ^ (prefixWord ++ tailWord_5454620).sum := by decide
  have hdescent : baseEnd_5454620 < baseStart_5454620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454670 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_5454670 : Nat := 118140960795 + 5454670 * 2 ^ 59
def prefixEnd_5454670 : Nat := 4983230072969 + 3 ^ 40 * 5454670 * 2
def baseEnd_5454670 : Nat := 933622507220092937413145

theorem tailTrace_5454670 : CollatzResearch.WordTrace tailWord_5454670 prefixEnd_5454670 933622507220092937413145 := by
  unfold tailWord_5454670
  simp only [CollatzResearch.WordTrace]
  refine ⟨24868519893583706039245183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132632106099113098875974309 24868519893583706039245183)
  ·
    refine ⟨37302779840375559058867775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24868519893583706039245183 37302779840375559058867775)
    ·
      refine ⟨55954169760563338588301663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37302779840375559058867775 55954169760563338588301663)
      ·
        refine ⟨83931254640845007882452495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55954169760563338588301663 83931254640845007882452495)
        ·
          refine ⟨125896881961267511823678743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83931254640845007882452495 125896881961267511823678743)
          ·
            refine ⟨188845322941901267735518115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125896881961267511823678743 188845322941901267735518115)
            ·
              refine ⟨283267984412851901603277173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188845322941901267735518115 283267984412851901603277173)
              ·
                refine ⟨26556373538704865775307235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 283267984412851901603277173 26556373538704865775307235)
                ·
                  refine ⟨39834560308057298662960853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26556373538704865775307235 39834560308057298662960853)
                  ·
                    refine ⟨933622507220092937413145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39834560308057298662960853 933622507220092937413145)
                    ·
                      rfl

theorem cell23_5454670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_5454670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454670 prefixEnd_5454670 := by exact prefixLift 5454670
  have htrace : WordTrace (prefixWord ++ tailWord_5454670) baseStart_5454670 baseEnd_5454670 := by
    simpa [prefixWord, tailWord_5454670, baseEnd_5454670] using wordTrace_append hprefix tailTrace_5454670
  have hstable : (prefixWord ++ tailWord_5454670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454670).length < 2 ^ (prefixWord ++ tailWord_5454670).sum := by decide
  have hdescent : baseEnd_5454670 < baseStart_5454670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454691 : List Nat := [1, 1, 1, 5, 3, 3, 2, 2, 5]
def baseStart_5454691 : Nat := 118140960795 + 5454691 * 2 ^ 59
def prefixEnd_5454691 : Nat := 4983230072969 + 3 ^ 40 * 5454691 * 2
def baseEnd_5454691 : Nat := 311208700528224803341871

theorem tailTrace_5454691 : CollatzResearch.WordTrace tailWord_5454691 prefixEnd_5454691 311208700528224803341871 := by
  unfold tailWord_5454691
  simp only [CollatzResearch.WordTrace]
  refine ⟨198948925081593568900475927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132632616721062379266983951 198948925081593568900475927)
  ·
    refine ⟨298423387622390353350713891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198948925081593568900475927 298423387622390353350713891)
    ·
      refine ⟨447635081433585530026070837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298423387622390353350713891 447635081433585530026070837)
      ·
        refine ⟨41965788884398643439944141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 447635081433585530026070837 41965788884398643439944141)
        ·
          refine ⟨15737170831649491289979053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41965788884398643439944141 15737170831649491289979053)
          ·
            refine ⟨5901439061868559233742145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15737170831649491289979053 5901439061868559233742145)
            ·
              refine ⟨4426079296401419425306609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5901439061868559233742145 4426079296401419425306609)
              ·
                refine ⟨3319559472301064568979957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4426079296401419425306609 3319559472301064568979957)
                ·
                  refine ⟨311208700528224803341871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3319559472301064568979957 311208700528224803341871)
                  ·
                    rfl

theorem cell23_5454691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 5].length) (baseStart_5454691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454691 prefixEnd_5454691 := by exact prefixLift 5454691
  have htrace : WordTrace (prefixWord ++ tailWord_5454691) baseStart_5454691 baseEnd_5454691 := by
    simpa [prefixWord, tailWord_5454691, baseEnd_5454691] using wordTrace_append hprefix tailTrace_5454691
  have hstable : (prefixWord ++ tailWord_5454691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454691).length < 2 ^ (prefixWord ++ tailWord_5454691).sum := by decide
  have hdescent : baseEnd_5454691 < baseStart_5454691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454707 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 1, 6, 2]
def baseStart_5454707 : Nat := 118140960795 + 5454707 * 2 ^ 59
def prefixEnd_5454707 : Nat := 4983230072969 + 3 ^ 40 * 5454707 * 2
def baseEnd_5454707 : Nat := 2800886520444495167476765

theorem tailTrace_5454707 : CollatzResearch.WordTrace tailWord_5454707 prefixEnd_5454707 2800886520444495167476765 := by
  unfold tailWord_5454707
  simp only [CollatzResearch.WordTrace]
  refine ⟨198949508649535603633058375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132633005766357069088705583 198949508649535603633058375)
  ·
    refine ⟨298424262974303405449587563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198949508649535603633058375 298424262974303405449587563)
    ·
      refine ⟨447636394461455108174381345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298424262974303405449587563 447636394461455108174381345)
      ·
        refine ⟨335727295846091331130786009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447636394461455108174381345 335727295846091331130786009)
        ·
          refine ⟨251795471884568498348089507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335727295846091331130786009 251795471884568498348089507)
          ·
            refine ⟨377693207826852747522134261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251795471884568498348089507 377693207826852747522134261)
            ·
              refine ⟨35408738233767445080200087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 377693207826852747522134261 35408738233767445080200087)
              ·
                refine ⟨53113107350651167620300131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35408738233767445080200087 53113107350651167620300131)
                ·
                  refine ⟨79669661025976751430450197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53113107350651167620300131 79669661025976751430450197)
                  ·
                    refine ⟨3734515360592660223302353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79669661025976751430450197 3734515360592660223302353)
                    ·
                      refine ⟨2800886520444495167476765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734515360592660223302353 2800886520444495167476765)
                      ·
                        rfl

theorem cell23_5454707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 6, 2].length) (baseStart_5454707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454707 prefixEnd_5454707 := by exact prefixLift 5454707
  have htrace : WordTrace (prefixWord ++ tailWord_5454707) baseStart_5454707 baseEnd_5454707 := by
    simpa [prefixWord, tailWord_5454707, baseEnd_5454707] using wordTrace_append hprefix tailTrace_5454707
  have hstable : (prefixWord ++ tailWord_5454707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454707).length < 2 ^ (prefixWord ++ tailWord_5454707).sum := by decide
  have hdescent : baseEnd_5454707 < baseStart_5454707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454717 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_5454717 : Nat := 118140960795 + 5454717 * 2 ^ 59
def prefixEnd_5454717 : Nat := 4983230072969 + 3 ^ 40 * 5454717 * 2
def baseEnd_5454717 : Nat := 933630551750346709450573

theorem tailTrace_5454717 : CollatzResearch.WordTrace tailWord_5454717 prefixEnd_5454717 933630551750346709450573 := by
  unfold tailWord_5454717
  simp only [CollatzResearch.WordTrace]
  refine ⟨198949873379499375340922405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132633248919666250227281603 198949873379499375340922405)
  ·
    refine ⟨37303101258656132876422951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198949873379499375340922405 37303101258656132876422951)
    ·
      refine ⟨55954651887984199314634427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37303101258656132876422951 55954651887984199314634427)
      ·
        refine ⟨83931977831976298971951641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55954651887984199314634427 83931977831976298971951641)
        ·
          refine ⟨62948983373982224228963731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83931977831976298971951641 62948983373982224228963731)
          ·
            refine ⟨94423475060973336343445597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62948983373982224228963731 94423475060973336343445597)
            ·
              refine ⟨35408803147865001128792099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94423475060973336343445597 35408803147865001128792099)
              ·
                refine ⟨53113204721797501693188149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35408803147865001128792099 53113204721797501693188149)
                ·
                  refine ⟨4979362942668515783736389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53113204721797501693188149 4979362942668515783736389)
                  ·
                    refine ⟨933630551750346709450573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4979362942668515783736389 933630551750346709450573)
                    ·
                      rfl

theorem cell23_5454717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_5454717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454717 prefixEnd_5454717 := by exact prefixLift 5454717
  have htrace : WordTrace (prefixWord ++ tailWord_5454717) baseStart_5454717 baseEnd_5454717 := by
    simpa [prefixWord, tailWord_5454717, baseEnd_5454717] using wordTrace_append hprefix tailTrace_5454717
  have hstable : (prefixWord ++ tailWord_5454717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454717).length < 2 ^ (prefixWord ++ tailWord_5454717).sum := by decide
  have hdescent : baseEnd_5454717 < baseStart_5454717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454720 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_5454720 : Nat := 118140960795 + 5454720 * 2 ^ 59
def prefixEnd_5454720 : Nat := 4983230072969 + 3 ^ 40 * 5454720 * 2
def baseEnd_5454720 : Nat := 2800893195693003616614205

theorem tailTrace_5454720 : CollatzResearch.WordTrace tailWord_5454720 prefixEnd_5454720 2800893195693003616614205 := by
  unfold tailWord_5454720
  simp only [CollatzResearch.WordTrace]
  refine ⟨99474991399244253426640807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132633321865659004568854409 99474991399244253426640807)
  ·
    refine ⟨149212487098866380139961211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99474991399244253426640807 149212487098866380139961211)
    ·
      refine ⟨223818730648299570209941817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149212487098866380139961211 223818730648299570209941817)
      ·
        refine ⟨167864047986224677657456363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223818730648299570209941817 167864047986224677657456363)
        ·
          refine ⟨251796071979337016486184545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167864047986224677657456363 251796071979337016486184545)
          ·
            refine ⟨188847053984502762364638409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251796071979337016486184545 188847053984502762364638409)
            ·
              refine ⟨141635290488377071773478807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188847053984502762364638409 141635290488377071773478807)
              ·
                refine ⟨212452935732565607660218211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141635290488377071773478807 212452935732565607660218211)
                ·
                  refine ⟨318679403598848411490327317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212452935732565607660218211 318679403598848411490327317)
                  ·
                    refine ⟨14938097043696019288609093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 318679403598848411490327317 14938097043696019288609093)
                    ·
                      refine ⟨2800893195693003616614205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14938097043696019288609093 2800893195693003616614205)
                      ·
                        rfl

theorem cell23_5454720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_5454720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454720 prefixEnd_5454720 := by exact prefixLift 5454720
  have htrace : WordTrace (prefixWord ++ tailWord_5454720) baseStart_5454720 baseEnd_5454720 := by
    simpa [prefixWord, tailWord_5454720, baseEnd_5454720] using wordTrace_append hprefix tailTrace_5454720
  have hstable : (prefixWord ++ tailWord_5454720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454720).length < 2 ^ (prefixWord ++ tailWord_5454720).sum := by decide
  have hdescent : baseEnd_5454720 < baseStart_5454720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454751 : List Nat := [1, 1, 2, 5, 2, 1, 2, 4, 1, 4]
def baseStart_5454751 : Nat := 118140960795 + 5454751 * 2 ^ 59
def prefixEnd_5454751 : Nat := 4983230072969 + 3 ^ 40 * 5454751 * 2
def baseEnd_5454751 : Nat := 933636371197764331775521

theorem tailTrace_5454751 : CollatzResearch.WordTrace tailWord_5454751 prefixEnd_5454751 933636371197764331775521 := by
  unfold tailWord_5454751
  simp only [CollatzResearch.WordTrace]
  refine ⟨198951113461376199147660107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132634075640917466098440071 198951113461376199147660107)
  ·
    refine ⟨298426670192064298721490161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198951113461376199147660107 298426670192064298721490161)
    ·
      refine ⟨223820002644048224041117621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298426670192064298721490161 223820002644048224041117621)
      ·
        refine ⟨20983125247879521003854777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223820002644048224041117621 20983125247879521003854777)
        ·
          refine ⟨15737343935909640752891083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20983125247879521003854777 15737343935909640752891083)
          ·
            refine ⟨23606015903864461129336625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15737343935909640752891083 23606015903864461129336625)
            ·
              refine ⟨17704511927898345847002469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23606015903864461129336625 17704511927898345847002469)
              ·
                refine ⟨3319595986480939846312963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17704511927898345847002469 3319595986480939846312963)
                ·
                  refine ⟨4979393979721409769469445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319595986480939846312963 4979393979721409769469445)
                  ·
                    refine ⟨933636371197764331775521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4979393979721409769469445 933636371197764331775521)
                    ·
                      rfl

theorem cell23_5454751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 4].length) (baseStart_5454751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454751 prefixEnd_5454751 := by exact prefixLift 5454751
  have htrace : WordTrace (prefixWord ++ tailWord_5454751) baseStart_5454751 baseEnd_5454751 := by
    simpa [prefixWord, tailWord_5454751, baseEnd_5454751] using wordTrace_append hprefix tailTrace_5454751
  have hstable : (prefixWord ++ tailWord_5454751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454751).length < 2 ^ (prefixWord ++ tailWord_5454751).sum := by decide
  have hdescent : baseEnd_5454751 < baseStart_5454751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454784 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 1, 5, 2]
def baseStart_5454784 : Nat := 118140960795 + 5454784 * 2 ^ 59
def prefixEnd_5454784 : Nat := 4983230072969 + 3 ^ 40 * 5454784 * 2
def baseEnd_5454784 : Nat := 2800926058454891366213911

theorem tailTrace_5454784 : CollatzResearch.WordTrace tailWord_5454784 prefixEnd_5454784 2800926058454891366213911 := by
  unfold tailWord_5454784
  simp only [CollatzResearch.WordTrace]
  refine ⟨99476158535128322891805703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132634878046837763855740937 99476158535128322891805703)
  ·
    refine ⟨149214237802692484337708555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99476158535128322891805703 149214237802692484337708555)
    ·
      refine ⟨223821356704038726506562833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149214237802692484337708555 223821356704038726506562833)
      ·
        refine ⟨167866017528029044879922125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223821356704038726506562833 167866017528029044879922125)
        ·
          refine ⟨62949756573010891829970797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167866017528029044879922125 62949756573010891829970797)
          ·
            refine ⟨23606158714879084436239049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62949756573010891829970797 23606158714879084436239049)
            ·
              refine ⟨17704619036159313327179287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23606158714879084436239049 17704619036159313327179287)
              ·
                refine ⟨26556928554238969990768931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17704619036159313327179287 26556928554238969990768931)
                ·
                  refine ⟨39835392831358454986153397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26556928554238969990768931 39835392831358454986153397)
                  ·
                    refine ⟨3734568077939855154951881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39835392831358454986153397 3734568077939855154951881)
                    ·
                      refine ⟨2800926058454891366213911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734568077939855154951881 2800926058454891366213911)
                      ·
                        rfl

theorem cell23_5454784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_5454784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454784 prefixEnd_5454784 := by exact prefixLift 5454784
  have htrace : WordTrace (prefixWord ++ tailWord_5454784) baseStart_5454784 baseEnd_5454784 := by
    simpa [prefixWord, tailWord_5454784, baseEnd_5454784] using wordTrace_append hprefix tailTrace_5454784
  have hstable : (prefixWord ++ tailWord_5454784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454784).length < 2 ^ (prefixWord ++ tailWord_5454784).sum := by decide
  have hdescent : baseEnd_5454784 < baseStart_5454784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454817 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_5454817 : Nat := 118140960795 + 5454817 * 2 ^ 59
def prefixEnd_5454817 : Nat := 4983230072969 + 3 ^ 40 * 5454817 * 2
def baseEnd_5454817 : Nat := 2800943003316489737101259

theorem tailTrace_5454817 : CollatzResearch.WordTrace tailWord_5454817 prefixEnd_5454817 2800943003316489737101259 := by
  unfold tailWord_5454817
  simp only [CollatzResearch.WordTrace]
  refine ⟨198953520679137092419562705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132635680452758061613041803 198953520679137092419562705)
  ·
    refine ⟨149215140509352819314672029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198953520679137092419562705 149215140509352819314672029)
    ·
      refine ⟨55955677691007307243002011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149215140509352819314672029 55955677691007307243002011)
      ·
        refine ⟨83933516536510960864503017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55955677691007307243002011 83933516536510960864503017)
        ·
          refine ⟨62950137402383220648377263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83933516536510960864503017 62950137402383220648377263)
          ·
            refine ⟨94425206103574830972565895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62950137402383220648377263 94425206103574830972565895)
            ·
              refine ⟨141637809155362246458848843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94425206103574830972565895 141637809155362246458848843)
              ·
                refine ⟨212456713733043369688273265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141637809155362246458848843 212456713733043369688273265)
                ·
                  refine ⟨159342535299782527266204949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212456713733043369688273265 159342535299782527266204949)
                  ·
                    refine ⟨7469181342177305965603357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 159342535299782527266204949 7469181342177305965603357)
                    ·
                      refine ⟨2800943003316489737101259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7469181342177305965603357 2800943003316489737101259)
                      ·
                        rfl

theorem cell23_5454817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_5454817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454817 prefixEnd_5454817 := by exact prefixLift 5454817
  have htrace : WordTrace (prefixWord ++ tailWord_5454817) baseStart_5454817 baseEnd_5454817 := by
    simpa [prefixWord, tailWord_5454817, baseEnd_5454817] using wordTrace_append hprefix tailTrace_5454817
  have hstable : (prefixWord ++ tailWord_5454817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454817).length < 2 ^ (prefixWord ++ tailWord_5454817).sum := by decide
  have hdescent : baseEnd_5454817 < baseStart_5454817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454831 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 4]
def baseStart_5454831 : Nat := 118140960795 + 5454831 * 2 ^ 59
def prefixEnd_5454831 : Nat := 4983230072969 + 3 ^ 40 * 5454831 * 2
def baseEnd_5454831 : Nat := 2800950192045652682326195

theorem tailTrace_5454831 : CollatzResearch.WordTrace tailWord_5454831 prefixEnd_5454831 2800950192045652682326195 := by
  unfold tailWord_5454831
  simp only [CollatzResearch.WordTrace]
  refine ⟨198954031301086372810572347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132636020867390915207048231 198954031301086372810572347)
  ·
    refine ⟨298431046951629559215858521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198954031301086372810572347 298431046951629559215858521)
    ·
      refine ⟨223823285213722169411893891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298431046951629559215858521 223823285213722169411893891)
      ·
        refine ⟨335734927820583254117840837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223823285213722169411893891 335734927820583254117840837)
        ·
          refine ⟨62950298966359360147095157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335734927820583254117840837 62950298966359360147095157)
          ·
            refine ⟨5901590528096190013790171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62950298966359360147095157 5901590528096190013790171)
            ·
              refine ⟨8852385792144285020685257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901590528096190013790171 8852385792144285020685257)
              ·
                refine ⟨6639289344108213765513943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8852385792144285020685257 6639289344108213765513943)
                ·
                  refine ⟨9958934016162320648270915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639289344108213765513943 9958934016162320648270915)
                  ·
                    refine ⟨14938401024243480972406373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9958934016162320648270915 14938401024243480972406373)
                    ·
                      refine ⟨2800950192045652682326195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14938401024243480972406373 2800950192045652682326195)
                      ·
                        rfl

theorem cell23_5454831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 4].length) (baseStart_5454831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454831 prefixEnd_5454831 := by exact prefixLift 5454831
  have htrace : WordTrace (prefixWord ++ tailWord_5454831) baseStart_5454831 baseEnd_5454831 := by
    simpa [prefixWord, tailWord_5454831, baseEnd_5454831] using wordTrace_append hprefix tailTrace_5454831
  have hstable : (prefixWord ++ tailWord_5454831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454831).length < 2 ^ (prefixWord ++ tailWord_5454831).sum := by decide
  have hdescent : baseEnd_5454831 < baseStart_5454831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454844 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_5454844 : Nat := 118140960795 + 5454844 * 2 ^ 59
def prefixEnd_5454844 : Nat := 4983230072969 + 3 ^ 40 * 5454844 * 2
def baseEnd_5454844 : Nat := 2800956867294161131463635

theorem tailTrace_5454844 : CollatzResearch.WordTrace tailWord_5454844 prefixEnd_5454844 2800956867294161131463635 := by
  unfold tailWord_5454844
  simp only [CollatzResearch.WordTrace]
  refine ⟨99477252725019638015397793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132636336966692850687197057 99477252725019638015397793)
  ·
    refine ⟨74607939543764728511548345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99477252725019638015397793 74607939543764728511548345)
    ·
      refine ⟨55955954657823546383661259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74607939543764728511548345 55955954657823546383661259)
      ·
        refine ⟨83933931986735319575491889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55955954657823546383661259 83933931986735319575491889)
        ·
          refine ⟨62950448990051489681618917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83933931986735319575491889 62950448990051489681618917)
          ·
            refine ⟨11803209185634654315303547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62950448990051489681618917 11803209185634654315303547)
            ·
              refine ⟨17704813778451981472955321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11803209185634654315303547 17704813778451981472955321)
              ·
                refine ⟨13278610333838986104716491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17704813778451981472955321 13278610333838986104716491)
                ·
                  refine ⟨19917915500758479157074737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13278610333838986104716491 19917915500758479157074737)
                  ·
                    refine ⟨14938436625568859367806053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19917915500758479157074737 14938436625568859367806053)
                    ·
                      refine ⟨2800956867294161131463635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14938436625568859367806053 2800956867294161131463635)
                      ·
                        rfl

theorem cell23_5454844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_5454844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454844 prefixEnd_5454844 := by exact prefixLift 5454844
  have htrace : WordTrace (prefixWord ++ tailWord_5454844) baseStart_5454844 baseEnd_5454844 := by
    simpa [prefixWord, tailWord_5454844, baseEnd_5454844] using wordTrace_append hprefix tailTrace_5454844
  have hstable : (prefixWord ++ tailWord_5454844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454844).length < 2 ^ (prefixWord ++ tailWord_5454844).sum := by decide
  have hdescent : baseEnd_5454844 < baseStart_5454844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454881 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_5454881 : Nat := 118140960795 + 5454881 * 2 ^ 59
def prefixEnd_5454881 : Nat := 4983230072969 + 3 ^ 40 * 5454881 * 2
def baseEnd_5454881 : Nat := 2800975866078377486700965

theorem tailTrace_5454881 : CollatzResearch.WordTrace tailWord_5454881 prefixEnd_5454881 2800975866078377486700965 := by
  unfold tailWord_5454881
  simp only [CollatzResearch.WordTrace]
  refine ⟨198955854950905231349892497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132637236633936820899928331 198955854950905231349892497)
  ·
    refine ⟨149216891213178923512419373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198955854950905231349892497 149216891213178923512419373)
    ·
      refine ⟨55956334204942096317157265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149216891213178923512419373 55956334204942096317157265)
      ·
        refine ⟨41967250653706572237867949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55956334204942096317157265 41967250653706572237867949)
        ·
          refine ⟨15737718995139964589200481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41967250653706572237867949 15737718995139964589200481)
          ·
            refine ⟨11803289246354973441900361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15737718995139964589200481 11803289246354973441900361)
            ·
              refine ⟨8852466934766230081425271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11803289246354973441900361 8852466934766230081425271)
              ·
                refine ⟨13278700402149345122137907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8852466934766230081425271 13278700402149345122137907)
                ·
                  refine ⟨19918050603224017683206861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13278700402149345122137907 19918050603224017683206861)
                  ·
                    refine ⟨7469268976209006631202573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19918050603224017683206861 7469268976209006631202573)
                    ·
                      refine ⟨2800975866078377486700965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7469268976209006631202573 2800975866078377486700965)
                      ·
                        rfl

theorem cell23_5454881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_5454881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454881 prefixEnd_5454881 := by exact prefixLift 5454881
  have htrace : WordTrace (prefixWord ++ tailWord_5454881) baseStart_5454881 baseEnd_5454881 := by
    simpa [prefixWord, tailWord_5454881, baseEnd_5454881] using wordTrace_append hprefix tailTrace_5454881
  have hstable : (prefixWord ++ tailWord_5454881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454881).length < 2 ^ (prefixWord ++ tailWord_5454881).sum := by decide
  have hdescent : baseEnd_5454881 < baseStart_5454881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454891 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 1, 3, 2]
def baseStart_5454891 : Nat := 118140960795 + 5454891 * 2 ^ 59
def prefixEnd_5454891 : Nat := 4983230072969 + 3 ^ 40 * 5454891 * 2
def baseEnd_5454891 : Nat := 2800981000884922447575919

theorem tailTrace_5454891 : CollatzResearch.WordTrace tailWord_5454891 prefixEnd_5454891 2800981000884922447575919 := by
  unfold tailWord_5454891
  simp only [CollatzResearch.WordTrace]
  refine ⟨198956219680869003057756527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132637479787246002038504351 198956219680869003057756527)
  ·
    refine ⟨298434329521303504586634791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198956219680869003057756527 298434329521303504586634791)
    ·
      refine ⟨447651494281955256879952187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298434329521303504586634791 447651494281955256879952187)
      ·
        refine ⟨671477241422932885319928281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447651494281955256879952187 671477241422932885319928281)
        ·
          refine ⟨503607931067199663989946211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671477241422932885319928281 503607931067199663989946211)
          ·
            refine ⟨755411896600799495984919317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503607931067199663989946211 755411896600799495984919317)
            ·
              refine ⟨35409932653162476374293093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 755411896600799495984919317 35409932653162476374293093)
              ·
                refine ⟨6639362372467964320179955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35409932653162476374293093 6639362372467964320179955)
                ·
                  refine ⟨9959043558701946480269933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639362372467964320179955 9959043558701946480269933)
                  ·
                    refine ⟨3734641334513229930101225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9959043558701946480269933 3734641334513229930101225)
                    ·
                      refine ⟨2800981000884922447575919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734641334513229930101225 2800981000884922447575919)
                      ·
                        rfl

theorem cell23_5454891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 3, 2].length) (baseStart_5454891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454891 prefixEnd_5454891 := by exact prefixLift 5454891
  have htrace : WordTrace (prefixWord ++ tailWord_5454891) baseStart_5454891 baseEnd_5454891 := by
    simpa [prefixWord, tailWord_5454891, baseEnd_5454891] using wordTrace_append hprefix tailTrace_5454891
  have hstable : (prefixWord ++ tailWord_5454891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454891).length < 2 ^ (prefixWord ++ tailWord_5454891).sum := by decide
  have hdescent : baseEnd_5454891 < baseStart_5454891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454894 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5454894 : Nat := 118140960795 + 5454894 * 2 ^ 59
def prefixEnd_5454894 : Nat := 4983230072969 + 3 ^ 40 * 5454894 * 2
def baseEnd_5454894 : Nat := 2800982541326885935838405

theorem tailTrace_5454894 : CollatzResearch.WordTrace tailWord_5454894 prefixEnd_5454894 2800982541326885935838405 := by
  unfold tailWord_5454894
  simp only [CollatzResearch.WordTrace]
  refine ⟨24869541137482266821264467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132637552733238756380077157 24869541137482266821264467)
  ·
    refine ⟨37304311706223400231896701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24869541137482266821264467 37304311706223400231896701)
    ·
      refine ⟨13989116889833775086961263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37304311706223400231896701 13989116889833775086961263)
      ·
        refine ⟨20983675334750662630441895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13989116889833775086961263 20983675334750662630441895)
        ·
          refine ⟨31475513002125993945662843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20983675334750662630441895 31475513002125993945662843)
          ·
            refine ⟨47213269503188990918494265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31475513002125993945662843 47213269503188990918494265)
            ·
              refine ⟨35409952127391743188870699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47213269503188990918494265 35409952127391743188870699)
              ·
                refine ⟨53114928191087614783306049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35409952127391743188870699 53114928191087614783306049)
                ·
                  refine ⟨39836196143315711087479537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53114928191087614783306049 39836196143315711087479537)
                  ·
                    refine ⟨29877147107486783315609653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39836196143315711087479537 29877147107486783315609653)
                    ·
                      refine ⟨2800982541326885935838405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29877147107486783315609653 2800982541326885935838405)
                      ·
                        rfl

theorem cell23_5454894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5454894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454894 prefixEnd_5454894 := by exact prefixLift 5454894
  have htrace : WordTrace (prefixWord ++ tailWord_5454894) baseStart_5454894 baseEnd_5454894 := by
    simpa [prefixWord, tailWord_5454894, baseEnd_5454894] using wordTrace_append hprefix tailTrace_5454894
  have hstable : (prefixWord ++ tailWord_5454894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454894).length < 2 ^ (prefixWord ++ tailWord_5454894).sum := by decide
  have hdescent : baseEnd_5454894 < baseStart_5454894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454897 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 1, 8]
def baseStart_5454897 : Nat := 118140960795 + 5454897 * 2 ^ 59
def prefixEnd_5454897 : Nat := 4983230072969 + 3 ^ 40 * 5454897 * 2
def baseEnd_5454897 : Nat := 933661360589616474700297

theorem tailTrace_5454897 : CollatzResearch.WordTrace tailWord_5454897 prefixEnd_5454897 933661360589616474700297 := by
  unfold tailWord_5454897
  simp only [CollatzResearch.WordTrace]
  refine ⟨198956438518847266082474945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132637625679231510721649963 198956438518847266082474945)
  ·
    refine ⟨149217328889135449561856209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198956438518847266082474945 149217328889135449561856209)
    ·
      refine ⟨111912996666851587171392157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149217328889135449561856209 111912996666851587171392157)
      ·
        refine ⟨41967373750069345189272059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111912996666851587171392157 41967373750069345189272059)
        ·
          refine ⟨62951060625104017783908089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41967373750069345189272059 62951060625104017783908089)
          ·
            refine ⟨47213295468828013337931067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62951060625104017783908089 47213295468828013337931067)
            ·
              refine ⟨70819943203242020006896601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47213295468828013337931067 70819943203242020006896601)
              ·
                refine ⟨53114957402431515005172451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70819943203242020006896601 53114957402431515005172451)
                ·
                  refine ⟨79672436103647272507758677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53114957402431515005172451 79672436103647272507758677)
                  ·
                    refine ⟨933661360589616474700297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79672436103647272507758677 933661360589616474700297)
                    ·
                      rfl

theorem cell23_5454897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_5454897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454897 prefixEnd_5454897 := by exact prefixLift 5454897
  have htrace : WordTrace (prefixWord ++ tailWord_5454897) baseStart_5454897 baseEnd_5454897 := by
    simpa [prefixWord, tailWord_5454897, baseEnd_5454897] using wordTrace_append hprefix tailTrace_5454897
  have hstable : (prefixWord ++ tailWord_5454897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454897).length < 2 ^ (prefixWord ++ tailWord_5454897).sum := by decide
  have hdescent : baseEnd_5454897 < baseStart_5454897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454908 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_5454908 : Nat := 118140960795 + 5454908 * 2 ^ 59
def prefixEnd_5454908 : Nat := 4983230072969 + 3 ^ 40 * 5454908 * 2
def baseEnd_5454908 : Nat := 2800989730056048881063341

theorem tailTrace_5454908 : CollatzResearch.WordTrace tailWord_5454908 prefixEnd_5454908 2800989730056048881063341 := by
  unfold tailWord_5454908
  simp only [CollatzResearch.WordTrace]
  refine ⟨99478419860903707480562689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132637893147871609974083585 99478419860903707480562689)
  ·
    refine ⟨74608814895677780610422017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99478419860903707480562689 74608814895677780610422017)
    ·
      refine ⟨55956611171758335457816513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74608814895677780610422017 55956611171758335457816513)
      ·
        refine ⟨41967458378818751593362385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55956611171758335457816513 41967458378818751593362385)
        ·
          refine ⟨31475593784114063695021789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41967458378818751593362385 31475593784114063695021789)
          ·
            refine ⟨11803347669042773885633171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31475593784114063695021789 11803347669042773885633171)
            ·
              refine ⟨17705021503564160828449757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11803347669042773885633171 17705021503564160828449757)
              ·
                refine ⟨6639383063836560310668659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17705021503564160828449757 6639383063836560310668659)
                ·
                  refine ⟨9959074595754840466002989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639383063836560310668659 9959074595754840466002989)
                  ·
                    refine ⟨3734652973408065174751121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9959074595754840466002989 3734652973408065174751121)
                    ·
                      refine ⟨2800989730056048881063341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734652973408065174751121 2800989730056048881063341)
                      ·
                        rfl

theorem cell23_5454908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_5454908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454908 prefixEnd_5454908 := by exact prefixLift 5454908
  have htrace : WordTrace (prefixWord ++ tailWord_5454908) baseStart_5454908 baseEnd_5454908 := by
    simpa [prefixWord, tailWord_5454908, baseEnd_5454908] using wordTrace_append hprefix tailTrace_5454908
  have hstable : (prefixWord ++ tailWord_5454908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454908).length < 2 ^ (prefixWord ++ tailWord_5454908).sum := by decide
  have hdescent : baseEnd_5454908 < baseStart_5454908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5454942 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_5454942 : Nat := 118140960795 + 5454942 * 2 ^ 59
def prefixEnd_5454942 : Nat := 4983230072969 + 3 ^ 40 * 5454942 * 2
def baseEnd_5454942 : Nat := 2801007188398301748038185

theorem tailTrace_5454942 : CollatzResearch.WordTrace tailWord_5454942 prefixEnd_5454942 2801007188398301748038185 := by
  unfold tailWord_5454942
  simp only [CollatzResearch.WordTrace]
  refine ⟨24869759975460529845982885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132638719869122825845242053 24869759975460529845982885)
  ·
    refine ⟨4663079995398849346121791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24869759975460529845982885 4663079995398849346121791)
    ·
      refine ⟨6994619993098274019182687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663079995398849346121791 6994619993098274019182687)
      ·
        refine ⟨10491929989647411028774031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6994619993098274019182687 10491929989647411028774031)
        ·
          refine ⟨15737894984471116543161047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10491929989647411028774031 15737894984471116543161047)
          ·
            refine ⟨23606842476706674814741571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15737894984471116543161047 23606842476706674814741571)
            ·
              refine ⟨35410263715060012222112357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23606842476706674814741571 35410263715060012222112357)
              ·
                refine ⟨6639424446573752291646067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35410263715060012222112357 6639424446573752291646067)
                ·
                  refine ⟨9959136669860628437469101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639424446573752291646067 9959136669860628437469101)
                  ·
                    refine ⟨3734676251197735664050913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9959136669860628437469101 3734676251197735664050913)
                    ·
                      refine ⟨2801007188398301748038185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734676251197735664050913 2801007188398301748038185)
                      ·
                        rfl

theorem cell23_5454942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_5454942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5454942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5454942 prefixEnd_5454942 := by exact prefixLift 5454942
  have htrace : WordTrace (prefixWord ++ tailWord_5454942) baseStart_5454942 baseEnd_5454942 := by
    simpa [prefixWord, tailWord_5454942, baseEnd_5454942] using wordTrace_append hprefix tailTrace_5454942
  have hstable : (prefixWord ++ tailWord_5454942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5454942).length < 2 ^ (prefixWord ++ tailWord_5454942).sum := by decide
  have hdescent : baseEnd_5454942 < baseStart_5454942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5454942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455031 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_5455031 : Nat := 118140960795 + 5455031 * 2 ^ 59
def prefixEnd_5455031 : Nat := 4983230072969 + 3 ^ 40 * 5455031 * 2
def baseEnd_5455031 : Nat := 2801052888176551899825275

theorem tailTrace_5455031 : CollatzResearch.WordTrace tailWord_5455031 prefixEnd_5455031 2801052888176551899825275 := by
  unfold tailWord_5455031
  simp only [CollatzResearch.WordTrace]
  refine ⟨198961325900361806967852947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132640883933574537978568631 198961325900361806967852947)
  ·
    refine ⟨298441988850542710451779421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198961325900361806967852947 298441988850542710451779421)
    ·
      refine ⟨111915745818953516419417283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298441988850542710451779421 111915745818953516419417283)
      ·
        refine ⟨167873618728430274629125925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111915745818953516419417283 167873618728430274629125925)
        ·
          refine ⟨31476303511580676492961111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167873618728430274629125925 31476303511580676492961111)
          ·
            refine ⟨47214455267371014739441667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31476303511580676492961111 47214455267371014739441667)
            ·
              refine ⟨70821682901056522109162501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47214455267371014739441667 70821682901056522109162501)
              ·
                refine ⟨13279065543948097895467969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70821682901056522109162501 13279065543948097895467969)
                ·
                  refine ⟨9959299157961073421600977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13279065543948097895467969 9959299157961073421600977)
                  ·
                    refine ⟨7469474368470805066200733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9959299157961073421600977 7469474368470805066200733)
                    ·
                      refine ⟨2801052888176551899825275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7469474368470805066200733 2801052888176551899825275)
                      ·
                        rfl

theorem cell23_5455031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_5455031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455031 prefixEnd_5455031 := by exact prefixLift 5455031
  have htrace : WordTrace (prefixWord ++ tailWord_5455031) baseStart_5455031 baseEnd_5455031 := by
    simpa [prefixWord, tailWord_5455031, baseEnd_5455031] using wordTrace_append hprefix tailTrace_5455031
  have hstable : (prefixWord ++ tailWord_5455031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455031).length < 2 ^ (prefixWord ++ tailWord_5455031).sum := by decide
  have hdescent : baseEnd_5455031 < baseStart_5455031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455062 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5455062 : Nat := 118140960795 + 5455062 * 2 ^ 59
def prefixEnd_5455062 : Nat := 4983230072969 + 3 ^ 40 * 5455062 * 2
def baseEnd_5455062 : Nat := 2801068806076841278537633

theorem tailTrace_5455062 : CollatzResearch.WordTrace tailWord_5455062 prefixEnd_5455062 2801068806076841278537633 := by
  unfold tailWord_5455062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12435153535203093703889465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132641637708832999508154293 12435153535203093703889465)
  ·
    refine ⟨9326365151402320277917099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12435153535203093703889465 9326365151402320277917099)
    ·
      refine ⟨13989547727103480416875649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9326365151402320277917099 13989547727103480416875649)
      ·
        refine ⟨10492160795327610312656737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13989547727103480416875649 10492160795327610312656737)
        ·
          refine ⟨7869120596495707734492553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10492160795327610312656737 7869120596495707734492553)
          ·
            refine ⟨5901840447371780800869415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7869120596495707734492553 5901840447371780800869415)
            ·
              refine ⟨8852760671057671201304123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901840447371780800869415 8852760671057671201304123)
              ·
                refine ⟨13279141006586506801956185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8852760671057671201304123 13279141006586506801956185)
                ·
                  refine ⟨9959355754939880101467139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13279141006586506801956185 9959355754939880101467139)
                  ·
                    refine ⟨14939033632409820152200709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9959355754939880101467139 14939033632409820152200709)
                    ·
                      refine ⟨2801068806076841278537633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14939033632409820152200709 2801068806076841278537633)
                      ·
                        rfl

theorem cell23_5455062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5455062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455062 prefixEnd_5455062 := by exact prefixLift 5455062
  have htrace : WordTrace (prefixWord ++ tailWord_5455062) baseStart_5455062 baseEnd_5455062 := by
    simpa [prefixWord, tailWord_5455062, baseEnd_5455062] using wordTrace_append hprefix tailTrace_5455062
  have hstable : (prefixWord ++ tailWord_5455062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455062).length < 2 ^ (prefixWord ++ tailWord_5455062).sum := by decide
  have hdescent : baseEnd_5455062 < baseStart_5455062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455118 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_5455118 : Nat := 118140960795 + 5455118 * 2 ^ 59
def prefixEnd_5455118 : Nat := 4983230072969 + 3 ^ 40 * 5455118 * 2
def baseEnd_5455118 : Nat := 2801097560993493059437375

theorem tailTrace_5455118 : CollatzResearch.WordTrace tailWord_5455118 prefixEnd_5455118 2801097560993493059437375 := by
  unfold tailWord_5455118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24870562381380827603283751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132642999367364413884180005 24870562381380827603283751)
  ·
    refine ⟨37305843572071241404925627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24870562381380827603283751 37305843572071241404925627)
    ·
      refine ⟨55958765358106862107388441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37305843572071241404925627 55958765358106862107388441)
      ·
        refine ⟨41969074018580146580541331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55958765358106862107388441 41969074018580146580541331)
        ·
          refine ⟨62953611027870219870811997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41969074018580146580541331 62953611027870219870811997)
          ·
            refine ⟨23607604135451332451554499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62953611027870219870811997 23607604135451332451554499)
            ·
              refine ⟨35411406203176998677331749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23607604135451332451554499 35411406203176998677331749)
              ·
                refine ⟨6639638663095687251999703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35411406203176998677331749 6639638663095687251999703)
                ·
                  refine ⟨9959457994643530877999555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639638663095687251999703 9959457994643530877999555)
                  ·
                    refine ⟨14939186991965296316999333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9959457994643530877999555 14939186991965296316999333)
                    ·
                      refine ⟨2801097560993493059437375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14939186991965296316999333 2801097560993493059437375)
                      ·
                        rfl

theorem cell23_5455118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_5455118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455118 prefixEnd_5455118 := by exact prefixLift 5455118
  have htrace : WordTrace (prefixWord ++ tailWord_5455118) baseStart_5455118 baseEnd_5455118 := by
    simpa [prefixWord, tailWord_5455118, baseEnd_5455118] using wordTrace_append hprefix tailTrace_5455118
  have hstable : (prefixWord ++ tailWord_5455118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455118).length < 2 ^ (prefixWord ++ tailWord_5455118).sum := by decide
  have hdescent : baseEnd_5455118 < baseStart_5455118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455141 : List Nat := [1, 3, 1, 2, 4, 3, 9]
def baseStart_5455141 : Nat := 118140960795 + 5455141 * 2 ^ 59
def prefixEnd_5455141 : Nat := 4983230072969 + 3 ^ 40 * 5455141 * 2
def baseEnd_5455141 : Nat := 34581597173438845301849

theorem tailTrace_5455141 : CollatzResearch.WordTrace tailWord_5455141 prefixEnd_5455141 34581597173438845301849 := by
  unfold tailWord_5455141
  simp only [CollatzResearch.WordTrace]
  refine ⟨198965337929963295754357277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132643558619975530502904851 198965337929963295754357277)
  ·
    refine ⟨74612001723736235907883979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198965337929963295754357277 74612001723736235907883979)
    ·
      refine ⟨111918002585604353861825969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74612001723736235907883979 111918002585604353861825969)
      ·
        refine ⟨83938501939203265396369477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111918002585604353861825969 83938501939203265396369477)
        ·
          refine ⟨15738469113600612261819277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83938501939203265396369477 15738469113600612261819277)
          ·
            refine ⟨5901925917600229598182229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15738469113600612261819277 5901925917600229598182229)
            ·
              refine ⟨34581597173438845301849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5901925917600229598182229 34581597173438845301849)
              ·
                rfl

theorem cell23_5455141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 9].length) (baseStart_5455141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455141 prefixEnd_5455141 := by exact prefixLift 5455141
  have htrace : WordTrace (prefixWord ++ tailWord_5455141) baseStart_5455141 baseEnd_5455141 := by
    simpa [prefixWord, tailWord_5455141, baseEnd_5455141] using wordTrace_append hprefix tailTrace_5455141
  have hstable : (prefixWord ++ tailWord_5455141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455141).length < 2 ^ (prefixWord ++ tailWord_5455141).sum := by decide
  have hdescent : baseEnd_5455141 < baseStart_5455141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455172 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_5455172 : Nat := 118140960795 + 5455172 * 2 ^ 59
def prefixEnd_5455172 : Nat := 4983230072969 + 3 ^ 40 * 5455172 * 2
def baseEnd_5455172 : Nat := 2801125288948835848162127

theorem tailTrace_5455172 : CollatzResearch.WordTrace tailWord_5455172 prefixEnd_5455172 2801125288948835848162127 := by
  unfold tailWord_5455172
  simp only [CollatzResearch.WordTrace]
  refine ⟨99483234296425494024367885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132644312395233992032490513 99483234296425494024367885)
  ·
    refine ⟨37306212861159560259137957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99483234296425494024367885 37306212861159560259137957)
    ·
      refine ⟨6994914911467417548588367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37306212861159560259137957 6994914911467417548588367)
      ·
        refine ⟨10492372367201126322882551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6994914911467417548588367 10492372367201126322882551)
        ·
          refine ⟨15738558550801689484323827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10492372367201126322882551 15738558550801689484323827)
          ·
            refine ⟨23607837826202534226485741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15738558550801689484323827 23607837826202534226485741)
            ·
              refine ⟨8852939184825950334932153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23607837826202534226485741 8852939184825950334932153)
              ·
                refine ⟨6639704388619462751199115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8852939184825950334932153 6639704388619462751199115)
                ·
                  refine ⟨9959556582929194126798673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639704388619462751199115 9959556582929194126798673)
                  ·
                    refine ⟨7469667437196895595099005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9959556582929194126798673 7469667437196895595099005)
                    ·
                      refine ⟨2801125288948835848162127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7469667437196895595099005 2801125288948835848162127)
                      ·
                        rfl

theorem cell23_5455172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_5455172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455172 prefixEnd_5455172 := by exact prefixLift 5455172
  have htrace : WordTrace (prefixWord ++ tailWord_5455172) baseStart_5455172 baseEnd_5455172 := by
    simpa [prefixWord, tailWord_5455172, baseEnd_5455172] using wordTrace_append hprefix tailTrace_5455172
  have hstable : (prefixWord ++ tailWord_5455172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455172).length < 2 ^ (prefixWord ++ tailWord_5455172).sum := by decide
  have hdescent : baseEnd_5455172 < baseStart_5455172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455202 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_5455202 : Nat := 118140960795 + 5455202 * 2 ^ 59
def prefixEnd_5455202 : Nat := 4983230072969 + 3 ^ 40 * 5455202 * 2
def baseEnd_5455202 : Nat := 2801140693368470730786989

theorem tailTrace_5455202 : CollatzResearch.WordTrace tailWord_5455202 prefixEnd_5455202 2801140693368470730786989 := by
  unfold tailWord_5455202
  simp only [CollatzResearch.WordTrace]
  refine ⟨49741890695685575793081965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132645041855161535448218573 49741890695685575793081965)
  ·
    refine ⟨18653209010882090922405737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49741890695685575793081965 18653209010882090922405737)
    ·
      refine ⟨13989906758161568191804303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18653209010882090922405737 13989906758161568191804303)
      ·
        refine ⟨20984860137242352287706455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13989906758161568191804303 20984860137242352287706455)
        ·
          refine ⟨31477290205863528431559683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20984860137242352287706455 31477290205863528431559683)
          ·
            refine ⟨47215935308795292647339525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31477290205863528431559683 47215935308795292647339525)
            ·
              refine ⟨8852987870399117371376161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47215935308795292647339525 8852987870399117371376161)
              ·
                refine ⟨6639740902799338028532121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8852987870399117371376161 6639740902799338028532121)
                ·
                  refine ⟨4979805677099503521399091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6639740902799338028532121 4979805677099503521399091)
                  ·
                    refine ⟨7469708515649255282098637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4979805677099503521399091 7469708515649255282098637)
                    ·
                      refine ⟨2801140693368470730786989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7469708515649255282098637 2801140693368470730786989)
                      ·
                        rfl

theorem cell23_5455202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_5455202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455202 prefixEnd_5455202 := by exact prefixLift 5455202
  have htrace : WordTrace (prefixWord ++ tailWord_5455202) baseStart_5455202 baseEnd_5455202 := by
    simpa [prefixWord, tailWord_5455202, baseEnd_5455202] using wordTrace_append hprefix tailTrace_5455202
  have hstable : (prefixWord ++ tailWord_5455202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455202).length < 2 ^ (prefixWord ++ tailWord_5455202).sum := by decide
  have hdescent : baseEnd_5455202 < baseStart_5455202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455246 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5455246 : Nat := 118140960795 + 5455246 * 2 ^ 59
def prefixEnd_5455246 : Nat := 4983230072969 + 3 ^ 40 * 5455246 * 2
def baseEnd_5455246 : Nat := 2801163286517268558636787

theorem tailTrace_5455246 : CollatzResearch.WordTrace tailWord_5455246 prefixEnd_5455246 2801163286517268558636787 := by
  unfold tailWord_5455246
  simp only [CollatzResearch.WordTrace]
  refine ⟨24871145949322862335866199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132646111729721932457953061 24871145949322862335866199)
  ·
    refine ⟨37306718923984293503799299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24871145949322862335866199 37306718923984293503799299)
    ·
      refine ⟨55960078385976440255698949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37306718923984293503799299 55960078385976440255698949)
      ·
        refine ⟨10492514697370582547943553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55960078385976440255698949 10492514697370582547943553)
        ·
          refine ⟨7869386023027936910957665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10492514697370582547943553 7869386023027936910957665)
          ·
            refine ⟨5902039517270952683218249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7869386023027936910957665 5902039517270952683218249)
            ·
              refine ⟨4426529637953214512413687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5902039517270952683218249 4426529637953214512413687)
              ·
                refine ⟨6639794456929821768620531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426529637953214512413687 6639794456929821768620531)
                ·
                  refine ⟨9959691685394732652930797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639794456929821768620531 9959691685394732652930797)
                  ·
                    refine ⟨3734884382023024744849049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9959691685394732652930797 3734884382023024744849049)
                    ·
                      refine ⟨2801163286517268558636787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3734884382023024744849049 2801163286517268558636787)
                      ·
                        rfl

theorem cell23_5455246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5455246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455246 prefixEnd_5455246 := by exact prefixLift 5455246
  have htrace : WordTrace (prefixWord ++ tailWord_5455246) baseStart_5455246 baseEnd_5455246 := by
    simpa [prefixWord, tailWord_5455246, baseEnd_5455246] using wordTrace_append hprefix tailTrace_5455246
  have hstable : (prefixWord ++ tailWord_5455246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455246).length < 2 ^ (prefixWord ++ tailWord_5455246).sum := by decide
  have hdescent : baseEnd_5455246 < baseStart_5455246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455258 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_5455258 : Nat := 118140960795 + 5455258 * 2 ^ 59
def prefixEnd_5455258 : Nat := 4983230072969 + 3 ^ 40 * 5455258 * 2
def baseEnd_5455258 : Nat := 2801169448285122511686731

theorem tailTrace_5455258 : CollatzResearch.WordTrace tailWord_5455258 prefixEnd_5455258 2801169448285122511686731 := by
  unfold tailWord_5455258
  simp only [CollatzResearch.WordTrace]
  refine ⟨49742401317634856184091607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132646403513692949824244285 49742401317634856184091607)
  ·
    refine ⟨74613601976452284276137411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49742401317634856184091607 74613601976452284276137411)
    ·
      refine ⟨111920402964678426414206117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74613601976452284276137411 111920402964678426414206117)
      ·
        refine ⟨20985075555877204952663647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111920402964678426414206117 20985075555877204952663647)
        ·
          refine ⟨31477613333815807428995471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20985075555877204952663647 31477613333815807428995471)
          ·
            refine ⟨47216420000723711143493207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31477613333815807428995471 47216420000723711143493207)
            ·
              refine ⟨70824630001085566715239811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47216420000723711143493207 70824630001085566715239811)
              ·
                refine ⟨106236945001628350072859717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70824630001085566715239811 106236945001628350072859717)
                ·
                  refine ⟨19919427187805315638661197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106236945001628350072859717 19919427187805315638661197)
                  ·
                    refine ⟨7469785195426993364497949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19919427187805315638661197 7469785195426993364497949)
                    ·
                      refine ⟨2801169448285122511686731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7469785195426993364497949 2801169448285122511686731)
                      ·
                        rfl

theorem cell23_5455258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_5455258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455258 prefixEnd_5455258 := by exact prefixLift 5455258
  have htrace : WordTrace (prefixWord ++ tailWord_5455258) baseStart_5455258 baseEnd_5455258 := by
    simpa [prefixWord, tailWord_5455258, baseEnd_5455258] using wordTrace_append hprefix tailTrace_5455258
  have hstable : (prefixWord ++ tailWord_5455258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455258).length < 2 ^ (prefixWord ++ tailWord_5455258).sum := by decide
  have hdescent : baseEnd_5455258 < baseStart_5455258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455311 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_5455311 : Nat := 118140960795 + 5455311 * 2 ^ 59
def prefixEnd_5455311 : Nat := 4983230072969 + 3 ^ 40 * 5455311 * 2
def baseEnd_5455311 : Nat := 2801196662759810804323987

theorem tailTrace_5455311 : CollatzResearch.WordTrace tailWord_5455311 prefixEnd_5455311 2801196662759810804323987 := by
  unfold tailWord_5455311
  simp only [CollatzResearch.WordTrace]
  refine ⟨198971538339347414788045787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132647692226231609858697191 198971538339347414788045787)
  ·
    refine ⟨298457307509021122182068681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198971538339347414788045787 298457307509021122182068681)
    ·
      refine ⟨223842980631765841636551511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298457307509021122182068681 223842980631765841636551511)
      ·
        refine ⟨335764470947648762454827267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223842980631765841636551511 335764470947648762454827267)
        ·
          refine ⟨503646706421473143682240901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335764470947648762454827267 503646706421473143682240901)
          ·
            refine ⟨94433757454026214440420169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 503646706421473143682240901 94433757454026214440420169)
            ·
              refine ⟨70825318090519660830315127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94433757454026214440420169 70825318090519660830315127)
              ·
                refine ⟨106237977135779491245472691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70825318090519660830315127 106237977135779491245472691)
                ·
                  refine ⟨159356965703669236868209037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106237977135779491245472691 159356965703669236868209037)
                  ·
                    refine ⟨59758862138875963825578389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159356965703669236868209037 59758862138875963825578389)
                    ·
                      refine ⟨2801196662759810804323987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59758862138875963825578389 2801196662759810804323987)
                      ·
                        rfl

theorem cell23_5455311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_5455311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455311 prefixEnd_5455311 := by exact prefixLift 5455311
  have htrace : WordTrace (prefixWord ++ tailWord_5455311) baseStart_5455311 baseEnd_5455311 := by
    simpa [prefixWord, tailWord_5455311, baseEnd_5455311] using wordTrace_append hprefix tailTrace_5455311
  have hstable : (prefixWord ++ tailWord_5455311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455311).length < 2 ^ (prefixWord ++ tailWord_5455311).sum := by decide
  have hdescent : baseEnd_5455311 < baseStart_5455311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455425 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5455425 : Nat := 118140960795 + 5455425 * 2 ^ 59
def prefixEnd_5455425 : Nat := 4983230072969 + 3 ^ 40 * 5455425 * 2
def baseEnd_5455425 : Nat := 2801255199554423358298463

theorem tailTrace_5455425 : CollatzResearch.WordTrace tailWord_5455425 prefixEnd_5455425 2801255199554423358298463 := by
  unfold tailWord_5455425
  simp only [CollatzResearch.WordTrace]
  refine ⟨198975696260934412257695729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132650464173956274838463819 198975696260934412257695729)
  ·
    refine ⟨149231772195700809193271797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198975696260934412257695729 149231772195700809193271797)
    ·
      refine ⟨13990478643346950861869231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149231772195700809193271797 13990478643346950861869231)
      ·
        refine ⟨20985717965020426292803847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13990478643346950861869231 20985717965020426292803847)
        ·
          refine ⟨31478576947530639439205771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20985717965020426292803847 31478576947530639439205771)
          ·
            refine ⟨47217865421295959158808657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31478576947530639439205771 47217865421295959158808657)
            ·
              refine ⟨35413399065971969369106493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47217865421295959158808657 35413399065971969369106493)
              ·
                refine ⟨13280024649739488513414935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35413399065971969369106493 13280024649739488513414935)
                ·
                  refine ⟨19920036974609232770122403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13280024649739488513414935 19920036974609232770122403)
                  ·
                    refine ⟨29880055461913849155183605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19920036974609232770122403 29880055461913849155183605)
                    ·
                      refine ⟨2801255199554423358298463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29880055461913849155183605 2801255199554423358298463)
                      ·
                        rfl

theorem cell23_5455425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5455425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455425 prefixEnd_5455425 := by exact prefixLift 5455425
  have htrace : WordTrace (prefixWord ++ tailWord_5455425) baseStart_5455425 baseEnd_5455425 := by
    simpa [prefixWord, tailWord_5455425, baseEnd_5455425] using wordTrace_append hprefix tailTrace_5455425
  have hstable : (prefixWord ++ tailWord_5455425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455425).length < 2 ^ (prefixWord ++ tailWord_5455425).sum := by decide
  have hdescent : baseEnd_5455425 < baseStart_5455425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455438 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_5455438 : Nat := 118140960795 + 5455438 * 2 ^ 59
def prefixEnd_5455438 : Nat := 4983230072969 + 3 ^ 40 * 5455438 * 2
def baseEnd_5455438 : Nat := 2801261874802931807435903

theorem tailTrace_5455438 : CollatzResearch.WordTrace tailWord_5455438 prefixEnd_5455438 2801261874802931807435903 := by
  unfold tailWord_5455438
  simp only [CollatzResearch.WordTrace]
  refine ⟨24872021301235914434739871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132650780273258210318612645 24872021301235914434739871)
  ·
    refine ⟨37308031951853871652109807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24872021301235914434739871 37308031951853871652109807)
    ·
      refine ⟨55962047927780807478164711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37308031951853871652109807 55962047927780807478164711)
      ·
        refine ⟨83943071891671211217247067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55962047927780807478164711 83943071891671211217247067)
        ·
          refine ⟨125914607837506816825870601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83943071891671211217247067 125914607837506816825870601)
          ·
            refine ⟨94435955878130112619402951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125914607837506816825870601 94435955878130112619402951)
            ·
              refine ⟨141653933817195168929104427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94435955878130112619402951 141653933817195168929104427)
              ·
                refine ⟨212480900725792753393656641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141653933817195168929104427 212480900725792753393656641)
                ·
                  refine ⟨159360675544344565045242481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212480900725792753393656641 159360675544344565045242481)
                  ·
                    refine ⟨119520506658258423783931861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159360675544344565045242481 119520506658258423783931861)
                    ·
                      refine ⟨2801261874802931807435903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119520506658258423783931861 2801261874802931807435903)
                      ·
                        rfl

theorem cell23_5455438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_5455438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455438 prefixEnd_5455438 := by exact prefixLift 5455438
  have htrace : WordTrace (prefixWord ++ tailWord_5455438) baseStart_5455438 baseEnd_5455438 := by
    simpa [prefixWord, tailWord_5455438, baseEnd_5455438] using wordTrace_append hprefix tailTrace_5455438
  have hstable : (prefixWord ++ tailWord_5455438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455438).length < 2 ^ (prefixWord ++ tailWord_5455438).sum := by decide
  have hdescent : baseEnd_5455438 < baseStart_5455438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455452 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_5455452 : Nat := 118140960795 + 5455452 * 2 ^ 59
def prefixEnd_5455452 : Nat := 4983230072969 + 3 ^ 40 * 5455452 * 2
def baseEnd_5455452 : Nat := 2801269063532094752660839

theorem tailTrace_5455452 : CollatzResearch.WordTrace tailWord_5455452 prefixEnd_5455452 2801269063532094752660839 := by
  unfold tailWord_5455452
  simp only [CollatzResearch.WordTrace]
  refine ⟨99488340515918297934464305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132651120687891063912619073 99488340515918297934464305)
  ·
    refine ⟨74616255386938723450848229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99488340515918297934464305 74616255386938723450848229)
    ·
      refine ⟨13990547885051010647034043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74616255386938723450848229 13990547885051010647034043)
      ·
        refine ⟨20985821827576515970551065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13990547885051010647034043 20985821827576515970551065)
        ·
          refine ⟨15739366370682386977913299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20985821827576515970551065 15739366370682386977913299)
          ·
            refine ⟨23609049556023580466869949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15739366370682386977913299 23609049556023580466869949)
            ·
              refine ⟨8853393583508842675076231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23609049556023580466869949 8853393583508842675076231)
              ·
                refine ⟨13280090375263264012614347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8853393583508842675076231 13280090375263264012614347)
                ·
                  refine ⟨19920135562894896018921521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13280090375263264012614347 19920135562894896018921521)
                  ·
                    refine ⟨14940101672171172014191141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19920135562894896018921521 14940101672171172014191141)
                    ·
                      refine ⟨2801269063532094752660839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14940101672171172014191141 2801269063532094752660839)
                      ·
                        rfl

theorem cell23_5455452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_5455452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455452 prefixEnd_5455452 := by exact prefixLift 5455452
  have htrace : WordTrace (prefixWord ++ tailWord_5455452) baseStart_5455452 baseEnd_5455452 := by
    simpa [prefixWord, tailWord_5455452, baseEnd_5455452] using wordTrace_append hprefix tailTrace_5455452
  have hstable : (prefixWord ++ tailWord_5455452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455452).length < 2 ^ (prefixWord ++ tailWord_5455452).sum := by decide
  have hdescent : baseEnd_5455452 < baseStart_5455452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455472 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 4, 1, 3]
def baseStart_5455472 : Nat := 118140960795 + 5455472 * 2 ^ 59
def prefixEnd_5455472 : Nat := 4983230072969 + 3 ^ 40 * 5455472 * 2
def baseEnd_5455472 : Nat := 2801279333145184674410747

theorem tailTrace_5455472 : CollatzResearch.WordTrace tailWord_5455472 prefixEnd_5455472 2801279333145184674410747 := by
  unfold tailWord_5455472
  simp only [CollatzResearch.WordTrace]
  refine ⟨99488705245882069642328335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132651606994509426189771113 99488705245882069642328335)
  ·
    refine ⟨149233057868823104463492503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99488705245882069642328335 149233057868823104463492503)
    ·
      refine ⟨223849586803234656695238755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149233057868823104463492503 223849586803234656695238755)
      ·
        refine ⟨335774380204851985042858133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223849586803234656695238755 335774380204851985042858133)
        ·
          refine ⟨15739424072102436798883975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 335774380204851985042858133 15739424072102436798883975)
          ·
            refine ⟨23609136108153655198325963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15739424072102436798883975 23609136108153655198325963)
            ·
              refine ⟨35413704162230482797488945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23609136108153655198325963 35413704162230482797488945)
              ·
                refine ⟨26560278121672862098116709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35413704162230482797488945 26560278121672862098116709)
                ·
                  refine ⟨4980052147813661643396883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26560278121672862098116709 4980052147813661643396883)
                  ·
                    refine ⟨7470078221720492465095325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4980052147813661643396883 7470078221720492465095325)
                    ·
                      refine ⟨2801279333145184674410747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7470078221720492465095325 2801279333145184674410747)
                      ·
                        rfl

theorem cell23_5455472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 1, 3].length) (baseStart_5455472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455472 prefixEnd_5455472 := by exact prefixLift 5455472
  have htrace : WordTrace (prefixWord ++ tailWord_5455472) baseStart_5455472 baseEnd_5455472 := by
    simpa [prefixWord, tailWord_5455472, baseEnd_5455472] using wordTrace_append hprefix tailTrace_5455472
  have hstable : (prefixWord ++ tailWord_5455472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455472).length < 2 ^ (prefixWord ++ tailWord_5455472).sum := by decide
  have hdescent : baseEnd_5455472 < baseStart_5455472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455506 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_5455506 : Nat := 118140960795 + 5455506 * 2 ^ 59
def prefixEnd_5455506 : Nat := 4983230072969 + 3 ^ 40 * 5455506 * 2
def baseEnd_5455506 : Nat := 2801296791487437541385591

theorem tailTrace_5455506 : CollatzResearch.WordTrace tailWord_5455506 prefixEnd_5455506 2801296791487437541385591 := by
  unfold tailWord_5455506
  simp only [CollatzResearch.WordTrace]
  refine ⟨49744662643410240772848593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132652433715760642060929581 49744662643410240772848593)
  ·
    refine ⟨37308496982557680579636445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49744662643410240772848593 37308496982557680579636445)
    ·
      refine ⟨13990686368459130217363667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37308496982557680579636445 13990686368459130217363667)
      ·
        refine ⟨20986029552688695326045501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13990686368459130217363667 20986029552688695326045501)
        ·
          refine ⟨7869761082258260747267063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20986029552688695326045501 7869761082258260747267063)
          ·
            refine ⟨11804641623387391120900595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869761082258260747267063 11804641623387391120900595)
            ·
              refine ⟨17706962435081086681350893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11804641623387391120900595 17706962435081086681350893)
              ·
                refine ⟨6640110913155407505506585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17706962435081086681350893 6640110913155407505506585)
                ·
                  refine ⟨4980083184866555629129939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6640110913155407505506585 4980083184866555629129939)
                  ·
                    refine ⟨7470124777299833443694909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4980083184866555629129939 7470124777299833443694909)
                    ·
                      refine ⟨2801296791487437541385591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7470124777299833443694909 2801296791487437541385591)
                      ·
                        rfl

theorem cell23_5455506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_5455506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455506 prefixEnd_5455506 := by exact prefixLift 5455506
  have htrace : WordTrace (prefixWord ++ tailWord_5455506) baseStart_5455506 baseEnd_5455506 := by
    simpa [prefixWord, tailWord_5455506, baseEnd_5455506] using wordTrace_append hprefix tailTrace_5455506
  have hstable : (prefixWord ++ tailWord_5455506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455506).length < 2 ^ (prefixWord ++ tailWord_5455506).sum := by decide
  have hdescent : baseEnd_5455506 < baseStart_5455506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455546 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2]
def baseStart_5455546 : Nat := 118140960795 + 5455546 * 2 ^ 59
def prefixEnd_5455546 : Nat := 4983230072969 + 3 ^ 40 * 5455546 * 2
def baseEnd_5455546 : Nat := 2801317330713617384885407

theorem tailTrace_5455546 : CollatzResearch.WordTrace tailWord_5455546 prefixEnd_5455546 2801317330713617384885407 := by
  unfold tailWord_5455546
  simp only [CollatzResearch.WordTrace]
  refine ⟨49745027373374012480712623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132653406328997366615233661 49745027373374012480712623)
  ·
    refine ⟨74617541060061018721068935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49745027373374012480712623 74617541060061018721068935)
    ·
      refine ⟨111926311590091528081603403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74617541060061018721068935 111926311590091528081603403)
      ·
        refine ⟨167889467385137292122405105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111926311590091528081603403 167889467385137292122405105)
        ·
          refine ⟨125917100538852969091803829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167889467385137292122405105 125917100538852969091803829)
          ·
            refine ⟨11804728175517465852356609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125917100538852969091803829 11804728175517465852356609)
            ·
              refine ⟨8853546131638099389267457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11804728175517465852356609 8853546131638099389267457)
              ·
                refine ⟨6640159598728574541950593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8853546131638099389267457 6640159598728574541950593)
                ·
                  refine ⟨4980119699046430906462945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6640159598728574541950593 4980119699046430906462945)
                  ·
                    refine ⟨3735089774284823179847209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4980119699046430906462945 3735089774284823179847209)
                    ·
                      refine ⟨2801317330713617384885407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3735089774284823179847209 2801317330713617384885407)
                      ·
                        rfl

theorem cell23_5455546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_5455546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455546 prefixEnd_5455546 := by exact prefixLift 5455546
  have htrace : WordTrace (prefixWord ++ tailWord_5455546) baseStart_5455546 baseEnd_5455546 := by
    simpa [prefixWord, tailWord_5455546, baseEnd_5455546] using wordTrace_append hprefix tailTrace_5455546
  have hstable : (prefixWord ++ tailWord_5455546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455546).length < 2 ^ (prefixWord ++ tailWord_5455546).sum := by decide
  have hdescent : baseEnd_5455546 < baseStart_5455546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455552 : List Nat := [2, 1, 1, 2, 4, 1, 3, 4, 5]
def baseStart_5455552 : Nat := 118140960795 + 5455552 * 2 ^ 59
def prefixEnd_5455552 : Nat := 4983230072969 + 3 ^ 40 * 5455552 * 2
def baseEnd_5455552 : Nat := 311257823510838262378931

theorem tailTrace_5455552 : CollatzResearch.WordTrace tailWord_5455552 prefixEnd_5455552 311257823510838262378931 := by
  unfold tailWord_5455552
  simp only [CollatzResearch.WordTrace]
  refine ⟨99490164165737156473784455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132653552220982875298379273 99490164165737156473784455)
  ·
    refine ⟨149235246248605734710676683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99490164165737156473784455 149235246248605734710676683)
    ·
      refine ⟨223852869372908602066015025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149235246248605734710676683 223852869372908602066015025)
      ·
        refine ⟨167889652029681451549511269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223852869372908602066015025 167889652029681451549511269)
        ·
          refine ⟨31479309755565272165533363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167889652029681451549511269 31479309755565272165533363)
          ·
            refine ⟨47218964633347908248300045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31479309755565272165533363 47218964633347908248300045)
            ·
              refine ⟨17707111737505465593112517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47218964633347908248300045 17707111737505465593112517)
              ·
                refine ⟨3320083450782274798708597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17707111737505465593112517 3320083450782274798708597)
                ·
                  refine ⟨311257823510838262378931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3320083450782274798708597 311257823510838262378931)
                  ·
                    rfl

theorem cell23_5455552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 5].length) (baseStart_5455552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455552 prefixEnd_5455552 := by exact prefixLift 5455552
  have htrace : WordTrace (prefixWord ++ tailWord_5455552) baseStart_5455552 baseEnd_5455552 := by
    simpa [prefixWord, tailWord_5455552, baseEnd_5455552] using wordTrace_append hprefix tailTrace_5455552
  have hstable : (prefixWord ++ tailWord_5455552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455552).length < 2 ^ (prefixWord ++ tailWord_5455552).sum := by decide
  have hdescent : baseEnd_5455552 < baseStart_5455552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455602 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5455602 : Nat := 118140960795 + 5455602 * 2 ^ 59
def prefixEnd_5455602 : Nat := 4983230072969 + 3 ^ 40 * 5455602 * 2
def baseEnd_5455602 : Nat := 2801346085630269165785149

theorem tailTrace_5455602 : CollatzResearch.WordTrace tailWord_5455602 prefixEnd_5455602 2801346085630269165785149 := by
  unfold tailWord_5455602
  simp only [CollatzResearch.WordTrace]
  refine ⟨49745537995323292871722265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132654767987528780991259373 49745537995323292871722265)
  ·
    refine ⟨37309153496492469653791699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49745537995323292871722265 37309153496492469653791699)
    ·
      refine ⟨55963730244738704480687549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37309153496492469653791699 55963730244738704480687549)
      ·
        refine ⟨20986398841777014180257831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55963730244738704480687549 20986398841777014180257831)
        ·
          refine ⟨31479598262665521270386747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20986398841777014180257831 31479598262665521270386747)
          ·
            refine ⟨47219397393998281905580121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31479598262665521270386747 47219397393998281905580121)
            ·
              refine ⟨35414548045498711429185091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47219397393998281905580121 35414548045498711429185091)
              ·
                refine ⟨53121822068248067143777637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35414548045498711429185091 53121822068248067143777637)
                ·
                  refine ⟨9960341637796512589458307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53121822068248067143777637 9960341637796512589458307)
                  ·
                    refine ⟨14940512456694768884187461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9960341637796512589458307 14940512456694768884187461)
                    ·
                      refine ⟨2801346085630269165785149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14940512456694768884187461 2801346085630269165785149)
                      ·
                        rfl

theorem cell23_5455602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5455602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455602 prefixEnd_5455602 := by exact prefixLift 5455602
  have htrace : WordTrace (prefixWord ++ tailWord_5455602) baseStart_5455602 baseEnd_5455602 := by
    simpa [prefixWord, tailWord_5455602, baseEnd_5455602] using wordTrace_append hprefix tailTrace_5455602
  have hstable : (prefixWord ++ tailWord_5455602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455602).length < 2 ^ (prefixWord ++ tailWord_5455602).sum := by decide
  have hdescent : baseEnd_5455602 < baseStart_5455602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455695 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_5455695 : Nat := 118140960795 + 5455695 * 2 ^ 59
def prefixEnd_5455695 : Nat := 4983230072969 + 3 ^ 40 * 5455695 * 2
def baseEnd_5455695 : Nat := 2801393839331137301922221

theorem tailTrace_5455695 : CollatzResearch.WordTrace tailWord_5455695 prefixEnd_5455695 2801393839331137301922221 := by
  unfold tailWord_5455695
  simp only [CollatzResearch.WordTrace]
  refine ⟨198985543969956248370024539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132657029313304165580016359 198985543969956248370024539)
  ·
    refine ⟨298478315954934372555036809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198985543969956248370024539 298478315954934372555036809)
    ·
      refine ⟨223858736966200779416277607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298478315954934372555036809 223858736966200779416277607)
      ·
        refine ⟨335788105449301169124416411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223858736966200779416277607 335788105449301169124416411)
        ·
          refine ⟨503682158173951753686624617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335788105449301169124416411 503682158173951753686624617)
          ·
            refine ⟨377761618630463815264968463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503682158173951753686624617 377761618630463815264968463)
            ·
              refine ⟨566642427945695722897452695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377761618630463815264968463 566642427945695722897452695)
              ·
                refine ⟨849963641918543584346179043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566642427945695722897452695 849963641918543584346179043)
                ·
                  refine ⟨1274945462877815376519268565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849963641918543584346179043 1274945462877815376519268565)
                  ·
                    refine ⟨29881534286198797887170357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1274945462877815376519268565 29881534286198797887170357)
                    ·
                      refine ⟨2801393839331137301922221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29881534286198797887170357 2801393839331137301922221)
                      ·
                        rfl

theorem cell23_5455695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_5455695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455695 prefixEnd_5455695 := by exact prefixLift 5455695
  have htrace : WordTrace (prefixWord ++ tailWord_5455695) baseStart_5455695 baseEnd_5455695 := by
    simpa [prefixWord, tailWord_5455695, baseEnd_5455695] using wordTrace_append hprefix tailTrace_5455695
  have hstable : (prefixWord ++ tailWord_5455695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455695).length < 2 ^ (prefixWord ++ tailWord_5455695).sum := by decide
  have hdescent : baseEnd_5455695 < baseStart_5455695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455715 : List Nat := [1, 1, 1, 5, 15]
def baseStart_5455715 : Nat := 118140960795 + 5455715 * 2 ^ 59
def prefixEnd_5455715 : Nat := 4983230072969 + 3 ^ 40 * 5455715 * 2
def baseEnd_5455715 : Nat := 3842803990321299346601

theorem tailTrace_5455715 : CollatzResearch.WordTrace tailWord_5455715 prefixEnd_5455715 3842803990321299346601 := by
  unfold tailWord_5455715
  simp only [CollatzResearch.WordTrace]
  refine ⟨198986273429883791785752599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132657515619922527857168399 198986273429883791785752599)
  ·
    refine ⟨298479410144825687678628899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198986273429883791785752599 298479410144825687678628899)
    ·
      refine ⟨447719115217238531517943349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298479410144825687678628899 447719115217238531517943349)
      ·
        refine ⟨41973667051616112329807189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 447719115217238531517943349 41973667051616112329807189)
        ·
          refine ⟨3842803990321299346601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 41973667051616112329807189 3842803990321299346601)
          ·
            rfl

theorem cell23_5455715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 15].length) (baseStart_5455715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455715 prefixEnd_5455715 := by exact prefixLift 5455715
  have htrace : WordTrace (prefixWord ++ tailWord_5455715) baseStart_5455715 baseEnd_5455715 := by
    simpa [prefixWord, tailWord_5455715, baseEnd_5455715] using wordTrace_append hprefix tailTrace_5455715
  have hstable : (prefixWord ++ tailWord_5455715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455715).length < 2 ^ (prefixWord ++ tailWord_5455715).sum := by decide
  have hdescent : baseEnd_5455715 < baseStart_5455715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455832 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_5455832 : Nat := 118140960795 + 5455832 * 2 ^ 59
def prefixEnd_5455832 : Nat := 4983230072969 + 3 ^ 40 * 5455832 * 2
def baseEnd_5455832 : Nat := 2801464186180803265909091

theorem tailTrace_5455832 : CollatzResearch.WordTrace tailWord_5455832 prefixEnd_5455832 2801464186180803265909091 := by
  unfold tailWord_5455832
  simp only [CollatzResearch.WordTrace]
  refine ⟨99495270385229960383880875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132660360513639947178507833 99495270385229960383880875)
  ·
    refine ⟨149242905577844940575821313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99495270385229960383880875 149242905577844940575821313)
    ·
      refine ⟨111932179183383705431865985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149242905577844940575821313 111932179183383705431865985)
      ·
        refine ⟨83949134387537779073899489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111932179183383705431865985 83949134387537779073899489)
        ·
          refine ⟨62961850790653334305424617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83949134387537779073899489 62961850790653334305424617)
          ·
            refine ⟨47221388092990000729068463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62961850790653334305424617 47221388092990000729068463)
            ·
              refine ⟨70832082139485001093602695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47221388092990000729068463 70832082139485001093602695)
              ·
                refine ⟨106248123209227501640404043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70832082139485001093602695 106248123209227501640404043)
                ·
                  refine ⟨159372184813841252460606065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106248123209227501640404043 159372184813841252460606065)
                  ·
                    refine ⟨119529138610380939345454549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159372184813841252460606065 119529138610380939345454549)
                    ·
                      refine ⟨2801464186180803265909091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119529138610380939345454549 2801464186180803265909091)
                      ·
                        rfl

theorem cell23_5455832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_5455832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455832 prefixEnd_5455832 := by exact prefixLift 5455832
  have htrace : WordTrace (prefixWord ++ tailWord_5455832) baseStart_5455832 baseEnd_5455832 := by
    simpa [prefixWord, tailWord_5455832, baseEnd_5455832] using wordTrace_append hprefix tailTrace_5455832
  have hstable : (prefixWord ++ tailWord_5455832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455832).length < 2 ^ (prefixWord ++ tailWord_5455832).sum := by decide
  have hdescent : baseEnd_5455832 < baseStart_5455832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455839 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 7]
def baseStart_5455839 : Nat := 118140960795 + 5455839 * 2 ^ 59
def prefixEnd_5455839 : Nat := 4983230072969 + 3 ^ 40 * 5455839 * 2
def baseEnd_5455839 : Nat := 311274197838376082057951

theorem tailTrace_5455839 : CollatzResearch.WordTrace tailWord_5455839 prefixEnd_5455839 311274197838376082057951 := by
  unfold tailWord_5455839
  simp only [CollatzResearch.WordTrace]
  refine ⟨198990796081434560963266571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132660530720956373975511047 198990796081434560963266571)
  ·
    refine ⟨298486194122151841444899857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198990796081434560963266571 298486194122151841444899857)
    ·
      refine ⟨223864645591613881083674893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298486194122151841444899857 223864645591613881083674893)
      ·
        refine ⟨83949242096855205406378085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223864645591613881083674893 83949242096855205406378085)
        ·
          refine ⟨15740482893160351013695891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83949242096855205406378085 15740482893160351013695891)
          ·
            refine ⟨23610724339740526520543837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15740482893160351013695891 23610724339740526520543837)
            ·
              refine ⟨8854021627402697445203939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23610724339740526520543837 8854021627402697445203939)
              ·
                refine ⟨13281032441104046167805909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8854021627402697445203939 13281032441104046167805909)
                ·
                  refine ⟨311274197838376082057951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13281032441104046167805909 311274197838376082057951)
                  ·
                    rfl

theorem cell23_5455839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 7].length) (baseStart_5455839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455839 prefixEnd_5455839 := by exact prefixLift 5455839
  have htrace : WordTrace (prefixWord ++ tailWord_5455839) baseStart_5455839 baseEnd_5455839 := by
    simpa [prefixWord, tailWord_5455839, baseEnd_5455839] using wordTrace_append hprefix tailTrace_5455839
  have hstable : (prefixWord ++ tailWord_5455839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455839).length < 2 ^ (prefixWord ++ tailWord_5455839).sum := by decide
  have hdescent : baseEnd_5455839 < baseStart_5455839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455852 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_5455852 : Nat := 118140960795 + 5455852 * 2 ^ 59
def prefixEnd_5455852 : Nat := 4983230072969 + 3 ^ 40 * 5455852 * 2
def baseEnd_5455852 : Nat := 933824818597964395886333

theorem tailTrace_5455852 : CollatzResearch.WordTrace tailWord_5455852 prefixEnd_5455852 933824818597964395886333 := by
  unfold tailWord_5455852
  simp only [CollatzResearch.WordTrace]
  refine ⟨99495635115193732091744905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132660846820258309455659873 99495635115193732091744905)
  ·
    refine ⟨74621726336395299068808679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99495635115193732091744905 74621726336395299068808679)
    ·
      refine ⟨111932589504592948603213019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74621726336395299068808679 111932589504592948603213019)
      ·
        refine ⟨167898884256889422904819529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111932589504592948603213019 167898884256889422904819529)
        ·
          refine ⟨125924163192667067178614647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167898884256889422904819529 125924163192667067178614647)
          ·
            refine ⟨188886244789000600767921971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125924163192667067178614647 188886244789000600767921971)
            ·
              refine ⟨283329367183500901151882957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188886244789000600767921971 283329367183500901151882957)
              ·
                refine ⟨106248512693812837931956109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283329367183500901151882957 106248512693812837931956109)
                ·
                  refine ⟨39843192260179814224483541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106248512693812837931956109 39843192260179814224483541)
                  ·
                    refine ⟨933824818597964395886333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39843192260179814224483541 933824818597964395886333)
                    ·
                      rfl

theorem cell23_5455852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_5455852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455852 prefixEnd_5455852 := by exact prefixLift 5455852
  have htrace : WordTrace (prefixWord ++ tailWord_5455852) baseStart_5455852 baseEnd_5455852 := by
    simpa [prefixWord, tailWord_5455852, baseEnd_5455852] using wordTrace_append hprefix tailTrace_5455852
  have hstable : (prefixWord ++ tailWord_5455852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455852).length < 2 ^ (prefixWord ++ tailWord_5455852).sum := by decide
  have hdescent : baseEnd_5455852 < baseStart_5455852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455869 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_5455869 : Nat := 118140960795 + 5455869 * 2 ^ 59
def prefixEnd_5455869 : Nat := 4983230072969 + 3 ^ 40 * 5455869 * 2
def baseEnd_5455869 : Nat := 933827728321673207048807

theorem tailTrace_5455869 : CollatzResearch.WordTrace tailWord_5455869 prefixEnd_5455869 933827728321673207048807 := by
  unfold tailWord_5455869
  simp only [CollatzResearch.WordTrace]
  refine ⟨198991890271325876086858661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132661260180883917391239107 198991890271325876086858661)
  ·
    refine ⟨37310979425873601766285999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198991890271325876086858661 37310979425873601766285999)
    ·
      refine ⟨55966469138810402649428999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37310979425873601766285999 55966469138810402649428999)
      ·
        refine ⟨83949703708215603974143499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55966469138810402649428999 83949703708215603974143499)
        ·
          refine ⟨125924555562323405961215249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83949703708215603974143499 125924555562323405961215249)
          ·
            refine ⟨94443416671742554470911437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125924555562323405961215249 94443416671742554470911437)
            ·
              refine ⟨35416281251903457926591789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94443416671742554470911437 35416281251903457926591789)
              ·
                refine ⟨13281105469463796722471921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35416281251903457926591789 13281105469463796722471921)
                ·
                  refine ⟨9960829102097847541853941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13281105469463796722471921 9960829102097847541853941)
                  ·
                    refine ⟨933827728321673207048807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9960829102097847541853941 933827728321673207048807)
                    ·
                      rfl

theorem cell23_5455869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_5455869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455869 prefixEnd_5455869 := by exact prefixLift 5455869
  have htrace : WordTrace (prefixWord ++ tailWord_5455869) baseStart_5455869 baseEnd_5455869 := by
    simpa [prefixWord, tailWord_5455869, baseEnd_5455869] using wordTrace_append hprefix tailTrace_5455869
  have hstable : (prefixWord ++ tailWord_5455869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455869).length < 2 ^ (prefixWord ++ tailWord_5455869).sum := by decide
  have hdescent : baseEnd_5455869 < baseStart_5455869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455879 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5455879 : Nat := 118140960795 + 5455879 * 2 ^ 59
def prefixEnd_5455879 : Nat := 4983230072969 + 3 ^ 40 * 5455879 * 2
def baseEnd_5455879 : Nat := 2801488319771564582021375

theorem tailTrace_5455879 : CollatzResearch.WordTrace tailWord_5455879 prefixEnd_5455879 2801488319771564582021375 := by
  unfold tailWord_5455879
  simp only [CollatzResearch.WordTrace]
  refine ⟨198992255001289647794722691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132661503334193098529815127 198992255001289647794722691)
  ·
    refine ⟨298488382501934471692084037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198992255001289647794722691 298488382501934471692084037)
    ·
      refine ⟨55966571719112713442265757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298488382501934471692084037 55966571719112713442265757)
      ·
        refine ⟨20987464394667267540849659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55966571719112713442265757 20987464394667267540849659)
        ·
          refine ⟨31481196592000901311274489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20987464394667267540849659 31481196592000901311274489)
          ·
            refine ⟨23610897444000675983455867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31481196592000901311274489 23610897444000675983455867)
            ·
              refine ⟨35416346166001013975183801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23610897444000675983455867 35416346166001013975183801)
              ·
                refine ⟨26562259624500760481387851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35416346166001013975183801 26562259624500760481387851)
                ·
                  refine ⟨39843389436751140722081777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26562259624500760481387851 39843389436751140722081777)
                  ·
                    refine ⟨29882542077563355541561333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39843389436751140722081777 29882542077563355541561333)
                    ·
                      refine ⟨2801488319771564582021375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29882542077563355541561333 2801488319771564582021375)
                      ·
                        rfl

theorem cell23_5455879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5455879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455879 prefixEnd_5455879 := by exact prefixLift 5455879
  have htrace : WordTrace (prefixWord ++ tailWord_5455879) baseStart_5455879 baseEnd_5455879 := by
    simpa [prefixWord, tailWord_5455879, baseEnd_5455879] using wordTrace_append hprefix tailTrace_5455879
  have hstable : (prefixWord ++ tailWord_5455879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455879).length < 2 ^ (prefixWord ++ tailWord_5455879).sum := by decide
  have hdescent : baseEnd_5455879 < baseStart_5455879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455959 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 5, 5]
def baseStart_5455959 : Nat := 118140960795 + 5455959 * 2 ^ 59
def prefixEnd_5455959 : Nat := 4983230072969 + 3 ^ 40 * 5455959 * 2
def baseEnd_5455959 : Nat := 933843132741308089673669

theorem tailTrace_5455959 : CollatzResearch.WordTrace tailWord_5455959 prefixEnd_5455959 933843132741308089673669 := by
  unfold tailWord_5455959
  simp only [CollatzResearch.WordTrace]
  refine ⟨198995172840999821457634931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132663448560666547638423287 198995172840999821457634931)
  ·
    refine ⟨298492759261499732186452397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198995172840999821457634931 298492759261499732186452397)
    ·
      refine ⟨111934784723062399569919649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298492759261499732186452397 111934784723062399569919649)
      ·
        refine ⟨83951088542296799677439737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111934784723062399569919649 83951088542296799677439737)
        ·
          refine ⟨62963316406722599758079803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83951088542296799677439737 62963316406722599758079803)
          ·
            refine ⟨94444974610083899637119705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62963316406722599758079803 94444974610083899637119705)
            ·
              refine ⟨70833730957562924727839779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94444974610083899637119705 70833730957562924727839779)
              ·
                refine ⟨106250596436344387091759669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70833730957562924727839779 106250596436344387091759669)
                ·
                  refine ⟨9960993415907286289852469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106250596436344387091759669 9960993415907286289852469)
                  ·
                    refine ⟨933843132741308089673669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9960993415907286289852469 933843132741308089673669)
                    ·
                      rfl

theorem cell23_5455959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_5455959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455959 prefixEnd_5455959 := by exact prefixLift 5455959
  have htrace : WordTrace (prefixWord ++ tailWord_5455959) baseStart_5455959 baseEnd_5455959 := by
    simpa [prefixWord, tailWord_5455959, baseEnd_5455959] using wordTrace_append hprefix tailTrace_5455959
  have hstable : (prefixWord ++ tailWord_5455959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455959).length < 2 ^ (prefixWord ++ tailWord_5455959).sum := by decide
  have hdescent : baseEnd_5455959 < baseStart_5455959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5455973 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_5455973 : Nat := 118140960795 + 5455973 * 2 ^ 59
def prefixEnd_5455973 : Nat := 4983230072969 + 3 ^ 40 * 5455973 * 2
def baseEnd_5455973 : Nat := 2801536586953087214245943

theorem tailTrace_5455973 : CollatzResearch.WordTrace tailWord_5455973 prefixEnd_5455973 2801536586953087214245943 := by
  unfold tailWord_5455973
  simp only [CollatzResearch.WordTrace]
  refine ⟨198995683462949101848644573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132663788975299401232429715 198995683462949101848644573)
  ·
    refine ⟨74623381298605913193241715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198995683462949101848644573 74623381298605913193241715)
    ·
      refine ⟨111935071947908869789862573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74623381298605913193241715 111935071947908869789862573)
      ·
        refine ⟨41975651980465826171198465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111935071947908869789862573 41975651980465826171198465)
        ·
          refine ⟨31481738985349369628398849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41975651980465826171198465 31481738985349369628398849)
          ·
            refine ⟨23611304239012027221299137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31481738985349369628398849 23611304239012027221299137)
            ·
              refine ⟨17708478179259020415974353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23611304239012027221299137 17708478179259020415974353)
              ·
                refine ⟨13281358634444265311980765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17708478179259020415974353 13281358634444265311980765)
                ·
                  refine ⟨4980509487916599491992787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13281358634444265311980765 4980509487916599491992787)
                  ·
                    refine ⟨7470764231874899237989181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4980509487916599491992787 7470764231874899237989181)
                    ·
                      refine ⟨2801536586953087214245943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7470764231874899237989181 2801536586953087214245943)
                      ·
                        rfl

theorem cell23_5455973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_5455973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5455973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5455973 prefixEnd_5455973 := by exact prefixLift 5455973
  have htrace : WordTrace (prefixWord ++ tailWord_5455973) baseStart_5455973 baseEnd_5455973 := by
    simpa [prefixWord, tailWord_5455973, baseEnd_5455973] using wordTrace_append hprefix tailTrace_5455973
  have hstable : (prefixWord ++ tailWord_5455973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5455973).length < 2 ^ (prefixWord ++ tailWord_5455973).sum := by decide
  have hdescent : baseEnd_5455973 < baseStart_5455973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5455973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456009 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_5456009 : Nat := 118140960795 + 5456009 * 2 ^ 59
def prefixEnd_5456009 : Nat := 4983230072969 + 3 ^ 40 * 5456009 * 2
def baseEnd_5456009 : Nat := 2801555072256649073395777

theorem tailTrace_5456009 : CollatzResearch.WordTrace tailWord_5456009 prefixEnd_5456009 2801555072256649073395777 := by
  unfold tailWord_5456009
  simp only [CollatzResearch.WordTrace]
  refine ⟨198996996490818679996955081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132664664327212453331303387 198996996490818679996955081)
  ·
    refine ⟨149247747368114009997716311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198996996490818679996955081 149247747368114009997716311)
    ·
      refine ⟨223871621052171014996574467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149247747368114009997716311 223871621052171014996574467)
      ·
        refine ⟨335807431578256522494861701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223871621052171014996574467 335807431578256522494861701)
        ·
          refine ⟨62963893420923097967786569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335807431578256522494861701 62963893420923097967786569)
          ·
            refine ⟨47222920065692323475839927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62963893420923097967786569 47222920065692323475839927)
            ·
              refine ⟨70834380098538485213759891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47222920065692323475839927 70834380098538485213759891)
              ·
                refine ⟨106251570147807727820639837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70834380098538485213759891 106251570147807727820639837)
                ·
                  refine ⟨39844338805427897932739939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106251570147807727820639837 39844338805427897932739939)
                  ·
                    refine ⟨59766508208141846899109909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39844338805427897932739939 59766508208141846899109909)
                    ·
                      refine ⟨2801555072256649073395777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59766508208141846899109909 2801555072256649073395777)
                      ·
                        rfl

theorem cell23_5456009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_5456009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456009 prefixEnd_5456009 := by exact prefixLift 5456009
  have htrace : WordTrace (prefixWord ++ tailWord_5456009) baseStart_5456009 baseEnd_5456009 := by
    simpa [prefixWord, tailWord_5456009, baseEnd_5456009] using wordTrace_append hprefix tailTrace_5456009
  have hstable : (prefixWord ++ tailWord_5456009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456009).length < 2 ^ (prefixWord ++ tailWord_5456009).sum := by decide
  have hdescent : baseEnd_5456009 < baseStart_5456009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456016 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 3]
def baseStart_5456016 : Nat := 118140960795 + 5456016 * 2 ^ 59
def prefixEnd_5456016 : Nat := 4983230072969 + 3 ^ 40 * 5456016 * 2
def baseEnd_5456016 : Nat := 2801558666621230546008245

theorem tailTrace_5456016 : CollatzResearch.WordTrace tailWord_5456016 prefixEnd_5456016 2801558666621230546008245 := by
  unfold tailWord_5456016
  simp only [CollatzResearch.WordTrace]
  refine ⟨99498625900896660096229951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132664834534528880128306601 99498625900896660096229951)
  ·
    refine ⟨149247938851344990144344927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99498625900896660096229951 149247938851344990144344927)
    ·
      refine ⟨223871908277017485216517391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149247938851344990144344927 223871908277017485216517391)
      ·
        refine ⟨335807862415526227824776087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223871908277017485216517391 335807862415526227824776087)
        ·
          refine ⟨503711793623289341737164131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335807862415526227824776087 503711793623289341737164131)
          ·
            refine ⟨755567690434934012605746197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503711793623289341737164131 755567690434934012605746197)
            ·
              refine ⟨35417235489137531840894353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 755567690434934012605746197 35417235489137531840894353)
              ·
                refine ⟨26562926616853148880670765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35417235489137531840894353 26562926616853148880670765)
                ·
                  refine ⟨9961097481319930830251537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26562926616853148880670765 9961097481319930830251537)
                  ·
                    refine ⟨7470823110989948122688653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9961097481319930830251537 7470823110989948122688653)
                    ·
                      refine ⟨2801558666621230546008245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7470823110989948122688653 2801558666621230546008245)
                      ·
                        rfl

theorem cell23_5456016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_5456016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456016 prefixEnd_5456016 := by exact prefixLift 5456016
  have htrace : WordTrace (prefixWord ++ tailWord_5456016) baseStart_5456016 baseEnd_5456016 := by
    simpa [prefixWord, tailWord_5456016, baseEnd_5456016] using wordTrace_append hprefix tailTrace_5456016
  have hstable : (prefixWord ++ tailWord_5456016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456016).length < 2 ^ (prefixWord ++ tailWord_5456016).sum := by decide
  have hdescent : baseEnd_5456016 < baseStart_5456016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456030 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_5456030 : Nat := 118140960795 + 5456030 * 2 ^ 59
def prefixEnd_5456030 : Nat := 4983230072969 + 3 ^ 40 * 5456030 * 2
def baseEnd_5456030 : Nat := 2801565855350393491233181

theorem tailTrace_5456030 : CollatzResearch.WordTrace tailWord_5456030 prefixEnd_5456030 2801565855350393491233181 := by
  unfold tailWord_5456030
  simp only [CollatzResearch.WordTrace]
  refine ⟨24874720302967825072933693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132665174949161733722313029 24874720302967825072933693)
  ·
    refine ⟨9328020113612934402350135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24874720302967825072933693 9328020113612934402350135)
    ·
      refine ⟨13992030170419401603525203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9328020113612934402350135 13992030170419401603525203)
      ·
        refine ⟨20988045255629102405287805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13992030170419401603525203 20988045255629102405287805)
        ·
          refine ⟨7870516970860913401982927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20988045255629102405287805 7870516970860913401982927)
          ·
            refine ⟨11805775456291370102974391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7870516970860913401982927 11805775456291370102974391)
            ·
              refine ⟨17708663184437055154461587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11805775456291370102974391 17708663184437055154461587)
              ·
                refine ⟨26562994776655582731692381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17708663184437055154461587 26562994776655582731692381)
                ·
                  refine ⟨9961123041245843524384643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26562994776655582731692381 9961123041245843524384643)
                  ·
                    refine ⟨14941684561868765286576965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9961123041245843524384643 14941684561868765286576965)
                    ·
                      refine ⟨2801565855350393491233181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14941684561868765286576965 2801565855350393491233181)
                      ·
                        rfl

theorem cell23_5456030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_5456030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456030 prefixEnd_5456030 := by exact prefixLift 5456030
  have htrace : WordTrace (prefixWord ++ tailWord_5456030) baseStart_5456030 baseEnd_5456030 := by
    simpa [prefixWord, tailWord_5456030, baseEnd_5456030] using wordTrace_append hprefix tailTrace_5456030
  have hstable : (prefixWord ++ tailWord_5456030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456030).length < 2 ^ (prefixWord ++ tailWord_5456030).sum := by decide
  have hdescent : baseEnd_5456030 < baseStart_5456030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456033 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_5456033 : Nat := 118140960795 + 5456033 * 2 ^ 59
def prefixEnd_5456033 : Nat := 4983230072969 + 3 ^ 40 * 5456033 * 2
def baseEnd_5456033 : Nat := 2801567395792356979495667

theorem tailTrace_5456033 : CollatzResearch.WordTrace tailWord_5456033 prefixEnd_5456033 2801567395792356979495667 := by
  unfold tailWord_5456033
  simp only [CollatzResearch.WordTrace]
  refine ⟨198997871842731732095828753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132665247895154488063885835 198997871842731732095828753)
  ·
    refine ⟨149248403882048799071871565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198997871842731732095828753 149248403882048799071871565)
    ·
      refine ⟨55968151455768299651951837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149248403882048799071871565 55968151455768299651951837)
      ·
        refine ⟨20988056795913112369481939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55968151455768299651951837 20988056795913112369481939)
        ·
          refine ⟨31482085193869668554222909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20988056795913112369481939 31482085193869668554222909)
          ·
            refine ⟨11805781947701125707833591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31482085193869668554222909 11805781947701125707833591)
            ·
              refine ⟨17708672921551688561750387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11805781947701125707833591 17708672921551688561750387)
              ·
                refine ⟨26563009382327532842625581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17708672921551688561750387 26563009382327532842625581)
                ·
                  refine ⟨9961128518372824815984593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26563009382327532842625581 9961128518372824815984593)
                  ·
                    refine ⟨7470846388779618611988445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9961128518372824815984593 7470846388779618611988445)
                    ·
                      refine ⟨2801567395792356979495667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7470846388779618611988445 2801567395792356979495667)
                      ·
                        rfl

theorem cell23_5456033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_5456033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456033 prefixEnd_5456033 := by exact prefixLift 5456033
  have htrace : WordTrace (prefixWord ++ tailWord_5456033) baseStart_5456033 baseEnd_5456033 := by
    simpa [prefixWord, tailWord_5456033, baseEnd_5456033] using wordTrace_append hprefix tailTrace_5456033
  have hstable : (prefixWord ++ tailWord_5456033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456033).length < 2 ^ (prefixWord ++ tailWord_5456033).sum := by decide
  have hdescent : baseEnd_5456033 < baseStart_5456033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456050 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_5456050 : Nat := 118140960795 + 5456050 * 2 ^ 59
def prefixEnd_5456050 : Nat := 4983230072969 + 3 ^ 40 * 5456050 * 2
def baseEnd_5456050 : Nat := 2801576124963483412983089

theorem tailTrace_5456050 : CollatzResearch.WordTrace tailWord_5456050 prefixEnd_5456050 2801576124963483412983089 := by
  unfold tailWord_5456050
  simp only [CollatzResearch.WordTrace]
  refine ⟨49749622970917535999799401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132665661255780095999465069 49749622970917535999799401)
  ·
    refine ⟨37312217228188151999849551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49749622970917535999799401 37312217228188151999849551)
    ·
      refine ⟨55968325842282227999774327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37312217228188151999849551 55968325842282227999774327)
      ·
        refine ⟨83952488763423341999661491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55968325842282227999774327 83952488763423341999661491)
        ·
          refine ⟨125928733145135012999492237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83952488763423341999661491 125928733145135012999492237)
          ·
            refine ⟨47223274929425629874809589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125928733145135012999492237 47223274929425629874809589)
            ·
              refine ⟨4427182024633652800763399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47223274929425629874809589 4427182024633652800763399)
              ·
                refine ⟨6640773036950479201145099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427182024633652800763399 6640773036950479201145099)
                ·
                  refine ⟨9961159555425718801717649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6640773036950479201145099 9961159555425718801717649)
                  ·
                    refine ⟨7470869666569289101288237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9961159555425718801717649 7470869666569289101288237)
                    ·
                      refine ⟨2801576124963483412983089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7470869666569289101288237 2801576124963483412983089)
                      ·
                        rfl

theorem cell23_5456050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_5456050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456050 prefixEnd_5456050 := by exact prefixLift 5456050
  have htrace : WordTrace (prefixWord ++ tailWord_5456050) baseStart_5456050 baseEnd_5456050 := by
    simpa [prefixWord, tailWord_5456050, baseEnd_5456050] using wordTrace_append hprefix tailTrace_5456050
  have hstable : (prefixWord ++ tailWord_5456050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456050).length < 2 ^ (prefixWord ++ tailWord_5456050).sum := by decide
  have hdescent : baseEnd_5456050 < baseStart_5456050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456053 : List Nat := [1, 3, 3, 4, 2, 10]
def baseStart_5456053 : Nat := 118140960795 + 5456053 * 2 ^ 59
def prefixEnd_5456053 : Nat := 4983230072969 + 3 ^ 40 * 5456053 * 2
def baseEnd_5456053 : Nat := 11529126195084143626525

theorem tailTrace_5456053 : CollatzResearch.WordTrace tailWord_5456053 prefixEnd_5456053 11529126195084143626525 := by
  unfold tailWord_5456053
  simp only [CollatzResearch.WordTrace]
  refine ⟨198998601302659275511556813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132665734201772850341037875 198998601302659275511556813)
  ·
    refine ⟨74624475488497228316833805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198998601302659275511556813 74624475488497228316833805)
    ·
      refine ⟨27984178308186460618812677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74624475488497228316833805 27984178308186460618812677)
      ·
        refine ⟨5247033432784961366027377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27984178308186460618812677 5247033432784961366027377)
        ·
          refine ⟨3935275074588721024520533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5247033432784961366027377 3935275074588721024520533)
          ·
            refine ⟨11529126195084143626525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3935275074588721024520533 11529126195084143626525)
            ·
              rfl

theorem cell23_5456053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 10].length) (baseStart_5456053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456053 prefixEnd_5456053 := by exact prefixLift 5456053
  have htrace : WordTrace (prefixWord ++ tailWord_5456053) baseStart_5456053 baseEnd_5456053 := by
    simpa [prefixWord, tailWord_5456053, baseEnd_5456053] using wordTrace_append hprefix tailTrace_5456053
  have hstable : (prefixWord ++ tailWord_5456053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456053).length < 2 ^ (prefixWord ++ tailWord_5456053).sum := by decide
  have hdescent : baseEnd_5456053 < baseStart_5456053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456064 : List Nat := [2, 1, 1, 2, 5, 1, 4, 2, 1, 2, 2]
def baseStart_5456064 : Nat := 118140960795 + 5456064 * 2 ^ 59
def prefixEnd_5456064 : Nat := 4983230072969 + 3 ^ 40 * 5456064 * 2
def baseEnd_5456064 : Nat := 2801583313692646358208025

theorem tailTrace_5456064 : CollatzResearch.WordTrace tailWord_5456064 prefixEnd_5456064 2801583313692646358208025 := by
  unfold tailWord_5456064
  simp only [CollatzResearch.WordTrace]
  refine ⟨99499501252809712195103623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132666001670412949593471497 99499501252809712195103623)
  ·
    refine ⟨149249251879214568292655435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99499501252809712195103623 149249251879214568292655435)
    ·
      refine ⟨223873877818821852438983153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149249251879214568292655435 223873877818821852438983153)
      ·
        refine ⟨167905408364116389329237365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223873877818821852438983153 167905408364116389329237365)
        ·
          refine ⟨15741132034135911499616003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167905408364116389329237365 15741132034135911499616003)
          ·
            refine ⟨23611698051203867249424005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15741132034135911499616003 23611698051203867249424005)
            ·
              refine ⟨4427193384600725109267001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23611698051203867249424005 4427193384600725109267001)
              ·
                refine ⟨3320395038450543831950251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4427193384600725109267001 3320395038450543831950251)
                ·
                  refine ⟨4980592557675815747925377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320395038450543831950251 4980592557675815747925377)
                  ·
                    refine ⟨3735444418256861810944033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4980592557675815747925377 3735444418256861810944033)
                    ·
                      refine ⟨2801583313692646358208025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3735444418256861810944033 2801583313692646358208025)
                      ·
                        rfl

theorem cell23_5456064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_5456064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456064 prefixEnd_5456064 := by exact prefixLift 5456064
  have htrace : WordTrace (prefixWord ++ tailWord_5456064) baseStart_5456064 baseEnd_5456064 := by
    simpa [prefixWord, tailWord_5456064, baseEnd_5456064] using wordTrace_append hprefix tailTrace_5456064
  have hstable : (prefixWord ++ tailWord_5456064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456064).length < 2 ^ (prefixWord ++ tailWord_5456064).sum := by decide
  have hdescent : baseEnd_5456064 < baseStart_5456064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456098 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5456098 : Nat := 118140960795 + 5456098 * 2 ^ 59
def prefixEnd_5456098 : Nat := 4983230072969 + 3 ^ 40 * 5456098 * 2
def baseEnd_5456098 : Nat := 2801600772034899225182869

theorem tailTrace_5456098 : CollatzResearch.WordTrace tailWord_5456098 prefixEnd_5456098 2801600772034899225182869 := by
  unfold tailWord_5456098
  simp only [CollatzResearch.WordTrace]
  refine ⟨49750060646874062049236237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132666828391664165464629965 49750060646874062049236237)
  ·
    refine ⟨18656272742577773268463589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49750060646874062049236237 18656272742577773268463589)
    ·
      refine ⟨3498051139233332487836923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18656272742577773268463589 3498051139233332487836923)
      ·
        refine ⟨5247076708849998731755385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3498051139233332487836923 5247076708849998731755385)
        ·
          refine ⟨3935307531637499048816539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5247076708849998731755385 3935307531637499048816539)
          ·
            refine ⟨5902961297456248573224809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935307531637499048816539 5902961297456248573224809)
            ·
              refine ⟨4427220973092186429918607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5902961297456248573224809 4427220973092186429918607)
              ·
                refine ⟨6640831459638279644877911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427220973092186429918607 6640831459638279644877911)
                ·
                  refine ⟨9961247189457419467316867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6640831459638279644877911 9961247189457419467316867)
                  ·
                    refine ⟨14941870784186129200975301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9961247189457419467316867 14941870784186129200975301)
                    ·
                      refine ⟨2801600772034899225182869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14941870784186129200975301 2801600772034899225182869)
                      ·
                        rfl

theorem cell23_5456098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5456098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456098 prefixEnd_5456098 := by exact prefixLift 5456098
  have htrace : WordTrace (prefixWord ++ tailWord_5456098) baseStart_5456098 baseEnd_5456098 := by
    simpa [prefixWord, tailWord_5456098, baseEnd_5456098] using wordTrace_append hprefix tailTrace_5456098
  have hstable : (prefixWord ++ tailWord_5456098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456098).length < 2 ^ (prefixWord ++ tailWord_5456098).sum := by decide
  have hdescent : baseEnd_5456098 < baseStart_5456098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456106 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_5456106 : Nat := 118140960795 + 5456106 * 2 ^ 59
def prefixEnd_5456106 : Nat := 4983230072969 + 3 ^ 40 * 5456106 * 2
def baseEnd_5456106 : Nat := 2801604879880135193882831

theorem tailTrace_5456106 : CollatzResearch.WordTrace tailWord_5456106 prefixEnd_5456106 2801604879880135193882831 := by
  unfold tailWord_5456106
  simp only [CollatzResearch.WordTrace]
  refine ⟨49750133592866816390809043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132667022914311510375490781 49750133592866816390809043)
  ·
    refine ⟨74625200389300224586213565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49750133592866816390809043 74625200389300224586213565)
    ·
      refine ⟨27984450145987584219830087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74625200389300224586213565 27984450145987584219830087)
      ·
        refine ⟨41976675218981376329745131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27984450145987584219830087 41976675218981376329745131)
        ·
          refine ⟨62965012828472064494617697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41976675218981376329745131 62965012828472064494617697)
          ·
            refine ⟨47223759621354048370963273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62965012828472064494617697 47223759621354048370963273)
            ·
              refine ⟨35417819716015536278222455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47223759621354048370963273 35417819716015536278222455)
              ·
                refine ⟨53126729574023304417333683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35417819716015536278222455 53126729574023304417333683)
                ·
                  refine ⟨79690094361034956626000525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53126729574023304417333683 79690094361034956626000525)
                  ·
                    refine ⟨29883785385388108734750197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79690094361034956626000525 29883785385388108734750197)
                    ·
                      refine ⟨2801604879880135193882831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29883785385388108734750197 2801604879880135193882831)
                      ·
                        rfl

theorem cell23_5456106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_5456106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456106 prefixEnd_5456106 := by exact prefixLift 5456106
  have htrace : WordTrace (prefixWord ++ tailWord_5456106) baseStart_5456106 baseEnd_5456106 := by
    simpa [prefixWord, tailWord_5456106, baseEnd_5456106] using wordTrace_append hprefix tailTrace_5456106
  have hstable : (prefixWord ++ tailWord_5456106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456106).length < 2 ^ (prefixWord ++ tailWord_5456106).sum := by decide
  have hdescent : baseEnd_5456106 < baseStart_5456106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456160 : List Nat := [2, 1, 1, 5, 2, 1, 3, 3, 5]
def baseStart_5456160 : Nat := 118140960795 + 5456160 * 2 ^ 59
def prefixEnd_5456160 : Nat := 4983230072969 + 3 ^ 40 * 5456160 * 2
def baseEnd_5456160 : Nat := 311292511981719775845287

theorem tailTrace_5456160 : CollatzResearch.WordTrace tailWord_5456160 prefixEnd_5456160 311292511981719775845287 := by
  unfold tailWord_5456160
  simp only [CollatzResearch.WordTrace]
  refine ⟨99501251956635816392850967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132668335942181088523801289 99501251956635816392850967)
  ·
    refine ⟨149251877934953724589276451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99501251956635816392850967 149251877934953724589276451)
    ·
      refine ⟨223877816902430586883914677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149251877934953724589276451 223877816902430586883914677)
      ·
        refine ⟨20988545334602867520367001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223877816902430586883914677 20988545334602867520367001)
        ·
          refine ⟨15741409000952150640275251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20988545334602867520367001 15741409000952150640275251)
          ·
            refine ⟨23612113501428225960412877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15741409000952150640275251 23612113501428225960412877)
            ·
              refine ⟨8854542563035584735154829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23612113501428225960412877 8854542563035584735154829)
              ·
                refine ⟨3320453461138344275683061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8854542563035584735154829 3320453461138344275683061)
                ·
                  refine ⟨311292511981719775845287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3320453461138344275683061 311292511981719775845287)
                  ·
                    rfl

theorem cell23_5456160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 5].length) (baseStart_5456160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456160 prefixEnd_5456160 := by exact prefixLift 5456160
  have htrace : WordTrace (prefixWord ++ tailWord_5456160) baseStart_5456160 baseEnd_5456160 := by
    simpa [prefixWord, tailWord_5456160, baseEnd_5456160] using wordTrace_append hprefix tailTrace_5456160
  have hstable : (prefixWord ++ tailWord_5456160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456160).length < 2 ^ (prefixWord ++ tailWord_5456160).sum := by decide
  have hdescent : baseEnd_5456160 < baseStart_5456160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456176 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_5456176 : Nat := 118140960795 + 5456176 * 2 ^ 59
def prefixEnd_5456176 : Nat := 4983230072969 + 3 ^ 40 * 5456176 * 2
def baseEnd_5456176 : Nat := 2801640823525949920007509

theorem tailTrace_5456176 : CollatzResearch.WordTrace tailWord_5456176 prefixEnd_5456176 2801640823525949920007509 := by
  unfold tailWord_5456176
  simp only [CollatzResearch.WordTrace]
  refine ⟨99501543740606833759142191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132668724987475778345522921 99501543740606833759142191)
  ·
    refine ⟨149252315610910250638713287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99501543740606833759142191 149252315610910250638713287)
    ·
      refine ⟨223878473416365375958069931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149252315610910250638713287 223878473416365375958069931)
      ·
        refine ⟨335817710124548063937104897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223878473416365375958069931 335817710124548063937104897)
        ·
          refine ⟨251863282593411047952828673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335817710124548063937104897 251863282593411047952828673)
          ·
            refine ⟨188897461945058285964621505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251863282593411047952828673 188897461945058285964621505)
            ·
              refine ⟨141673096458793714473466129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188897461945058285964621505 141673096458793714473466129)
              ·
                refine ⟨106254822344095285855099597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141673096458793714473466129 106254822344095285855099597)
                ·
                  refine ⟨39845558379035732195662349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106254822344095285855099597 39845558379035732195662349)
                  ·
                    refine ⟨14942084392138399573373381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39845558379035732195662349 14942084392138399573373381)
                    ·
                      refine ⟨2801640823525949920007509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14942084392138399573373381 2801640823525949920007509)
                      ·
                        rfl

theorem cell23_5456176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_5456176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456176 prefixEnd_5456176 := by exact prefixLift 5456176
  have htrace : WordTrace (prefixWord ++ tailWord_5456176) baseStart_5456176 baseEnd_5456176 := by
    simpa [prefixWord, tailWord_5456176, baseEnd_5456176] using wordTrace_append hprefix tailTrace_5456176
  have hstable : (prefixWord ++ tailWord_5456176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456176).length < 2 ^ (prefixWord ++ tailWord_5456176).sum := by decide
  have hdescent : baseEnd_5456176 < baseStart_5456176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456177 : List Nat := [1, 2, 2, 3, 4, 1, 3, 2, 5]
def baseStart_5456177 : Nat := 118140960795 + 5456177 * 2 ^ 59
def prefixEnd_5456177 : Nat := 4983230072969 + 3 ^ 40 * 5456177 * 2
def baseEnd_5456177 : Nat := 311293481889622712899445

theorem tailTrace_5456177 : CollatzResearch.WordTrace tailWord_5456177 prefixEnd_5456177 311293481889622712899445 := by
  unfold tailWord_5456177
  simp only [CollatzResearch.WordTrace]
  refine ⟨199003123954210044689070785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132668749302806696459380523 199003123954210044689070785)
  ·
    refine ⟨149252342965657533516803089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199003123954210044689070785 149252342965657533516803089)
    ·
      refine ⟨111939257224243150137602317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149252342965657533516803089 111939257224243150137602317)
      ·
        refine ⟨41977221459091181301600869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111939257224243150137602317 41977221459091181301600869)
        ·
          refine ⟨7870729023579596494050163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41977221459091181301600869 7870729023579596494050163)
          ·
            refine ⟨11806093535369394741075245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7870729023579596494050163 11806093535369394741075245)
            ·
              refine ⟨4427285075763523027903217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11806093535369394741075245 4427285075763523027903217)
              ·
                refine ⟨3320463806822642270927413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4427285075763523027903217 3320463806822642270927413)
                ·
                  refine ⟨311293481889622712899445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3320463806822642270927413 311293481889622712899445)
                  ·
                    rfl

theorem cell23_5456177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 5].length) (baseStart_5456177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456177 prefixEnd_5456177 := by exact prefixLift 5456177
  have htrace : WordTrace (prefixWord ++ tailWord_5456177) baseStart_5456177 baseEnd_5456177 := by
    simpa [prefixWord, tailWord_5456177, baseEnd_5456177] using wordTrace_append hprefix tailTrace_5456177
  have hstable : (prefixWord ++ tailWord_5456177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456177).length < 2 ^ (prefixWord ++ tailWord_5456177).sum := by decide
  have hdescent : baseEnd_5456177 < baseStart_5456177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456216 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 8]
def baseStart_5456216 : Nat := 118140960795 + 5456216 * 2 ^ 59
def prefixEnd_5456216 : Nat := 4983230072969 + 3 ^ 40 * 5456216 * 2
def baseEnd_5456216 : Nat := 311295706972458862611925

theorem tailTrace_5456216 : CollatzResearch.WordTrace tailWord_5456216 prefixEnd_5456216 311295706972458862611925 := by
  unfold tailWord_5456216
  simp only [CollatzResearch.WordTrace]
  refine ⟨99502273200534377174870251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132669697600712502899827001 99502273200534377174870251)
  ·
    refine ⟨149253409800801565762305377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99502273200534377174870251 149253409800801565762305377)
    ·
      refine ⟨111940057350601174321729033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149253409800801565762305377 111940057350601174321729033)
      ·
        refine ⟨83955043012950880741296775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111940057350601174321729033 83955043012950880741296775)
        ·
          refine ⟨125932564519426321111945163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83955043012950880741296775 125932564519426321111945163)
          ·
            refine ⟨188898846779139481667917745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125932564519426321111945163 188898846779139481667917745)
            ·
              refine ⟨141674135084354611250938309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188898846779139481667917745 141674135084354611250938309)
              ·
                refine ⟨26563900328316489609550933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141674135084354611250938309 26563900328316489609550933)
                ·
                  refine ⟨311295706972458862611925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26563900328316489609550933 311295706972458862611925)
                  ·
                    rfl

theorem cell23_5456216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 8].length) (baseStart_5456216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456216 prefixEnd_5456216 := by exact prefixLift 5456216
  have htrace : WordTrace (prefixWord ++ tailWord_5456216) baseStart_5456216 baseEnd_5456216 := by
    simpa [prefixWord, tailWord_5456216, baseEnd_5456216] using wordTrace_append hprefix tailTrace_5456216
  have hstable : (prefixWord ++ tailWord_5456216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456216).length < 2 ^ (prefixWord ++ tailWord_5456216).sum := by decide
  have hdescent : baseEnd_5456216 < baseStart_5456216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456233 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 6]
def baseStart_5456233 : Nat := 118140960795 + 5456233 * 2 ^ 59
def prefixEnd_5456233 : Nat := 4983230072969 + 3 ^ 40 * 5456233 * 2
def baseEnd_5456233 : Nat := 311296676880361799666083

theorem tailTrace_5456233 : CollatzResearch.WordTrace tailWord_5456233 prefixEnd_5456233 311296676880361799666083 := by
  unfold tailWord_5456233
  simp only [CollatzResearch.WordTrace]
  refine ⟨199005166442007166253109353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132670110961338110835406235 199005166442007166253109353)
  ·
    refine ⟨149253874831505374689832015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199005166442007166253109353 149253874831505374689832015)
    ·
      refine ⟨223880812247258062034748023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149253874831505374689832015 223880812247258062034748023)
      ·
        refine ⟨335821218370887093052122035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223880812247258062034748023 335821218370887093052122035)
        ·
          refine ⟨503731827556330639578183053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335821218370887093052122035 503731827556330639578183053)
          ·
            refine ⟨188899435333623989841818645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 503731827556330639578183053 188899435333623989841818645)
            ·
              refine ⟨8854661031263624523835249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188899435333623989841818645 8854661031263624523835249)
              ·
                refine ⟨6640995773447718392876437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8854661031263624523835249 6640995773447718392876437)
                ·
                  refine ⟨311296676880361799666083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6640995773447718392876437 311296676880361799666083)
                  ·
                    rfl

theorem cell23_5456233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 6].length) (baseStart_5456233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456233 prefixEnd_5456233 := by exact prefixLift 5456233
  have htrace : WordTrace (prefixWord ++ tailWord_5456233) baseStart_5456233 baseEnd_5456233 := by
    simpa [prefixWord, tailWord_5456233, baseEnd_5456233] using wordTrace_append hprefix tailTrace_5456233
  have hstable : (prefixWord ++ tailWord_5456233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456233).length < 2 ^ (prefixWord ++ tailWord_5456233).sum := by decide
  have hdescent : baseEnd_5456233 < baseStart_5456233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456237 : List Nat := [1, 5, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_5456237 : Nat := 118140960795 + 5456237 * 2 ^ 59
def prefixEnd_5456237 : Nat := 4983230072969 + 3 ^ 40 * 5456237 * 2
def baseEnd_5456237 : Nat := 933890715281958060448243

theorem tailTrace_5456237 : CollatzResearch.WordTrace tailWord_5456237 prefixEnd_5456237 933890715281958060448243 := by
  unfold tailWord_5456237
  simp only [CollatzResearch.WordTrace]
  refine ⟨199005312333992674936254965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132670208222661783290836643 199005312333992674936254965)
  ·
    refine ⟨18656748031311813275273903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199005312333992674936254965 18656748031311813275273903)
    ·
      refine ⟨27985122046967719912910855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18656748031311813275273903 27985122046967719912910855)
      ·
        refine ⟨41977683070451579869366283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27985122046967719912910855 41977683070451579869366283)
        ·
          refine ⟨62966524605677369804049425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41977683070451579869366283 62966524605677369804049425)
          ·
            refine ⟨47224893454258027353037069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62966524605677369804049425 47224893454258027353037069)
            ·
              refine ⟨17709335045346760257388901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47224893454258027353037069 17709335045346760257388901)
              ·
                refine ⟨3320500321002517548260419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17709335045346760257388901 3320500321002517548260419)
                ·
                  refine ⟨4980750481503776322390629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320500321002517548260419 4980750481503776322390629)
                  ·
                    refine ⟨933890715281958060448243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4980750481503776322390629 933890715281958060448243)
                    ·
                      rfl

theorem cell23_5456237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_5456237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456237 prefixEnd_5456237 := by exact prefixLift 5456237
  have htrace : WordTrace (prefixWord ++ tailWord_5456237) baseStart_5456237 baseEnd_5456237 := by
    simpa [prefixWord, tailWord_5456237, baseEnd_5456237] using wordTrace_append hprefix tailTrace_5456237
  have hstable : (prefixWord ++ tailWord_5456237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456237).length < 2 ^ (prefixWord ++ tailWord_5456237).sum := by decide
  have hdescent : baseEnd_5456237 < baseStart_5456237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456263 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 3, 5]
def baseStart_5456263 : Nat := 118140960795 + 5456263 * 2 ^ 59
def prefixEnd_5456263 : Nat := 4983230072969 + 3 ^ 40 * 5456263 * 2
def baseEnd_5456263 : Nat := 933895165447630359873203

theorem tailTrace_5456263 : CollatzResearch.WordTrace tailWord_5456263 prefixEnd_5456263 933895165447630359873203 := by
  unfold tailWord_5456263
  simp only [CollatzResearch.WordTrace]
  refine ⟨199006260631898481376701443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132670840421265654251134295 199006260631898481376701443)
  ·
    refine ⟨298509390947847722065052165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199006260631898481376701443 298509390947847722065052165)
    ·
      refine ⟨55970510802721447887197281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298509390947847722065052165 55970510802721447887197281)
      ·
        refine ⟨41977883102041085915397961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55970510802721447887197281 41977883102041085915397961)
        ·
          refine ⟨31483412326530814436548471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41977883102041085915397961 31483412326530814436548471)
          ·
            refine ⟨47225118489796221654822707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31483412326530814436548471 47225118489796221654822707)
            ·
              refine ⟨70837677734694332482234061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47225118489796221654822707 70837677734694332482234061)
              ·
                refine ⟨26564129150510374680837773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70837677734694332482234061 26564129150510374680837773)
                ·
                  refine ⟨9961548431441390505314165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26564129150510374680837773 9961548431441390505314165)
                  ·
                    refine ⟨933895165447630359873203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9961548431441390505314165 933895165447630359873203)
                    ·
                      rfl

theorem cell23_5456263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_5456263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456263 prefixEnd_5456263 := by exact prefixLift 5456263
  have htrace : WordTrace (prefixWord ++ tailWord_5456263) baseStart_5456263 baseEnd_5456263 := by
    simpa [prefixWord, tailWord_5456263, baseEnd_5456263] using wordTrace_append hprefix tailTrace_5456263
  have hstable : (prefixWord ++ tailWord_5456263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456263).length < 2 ^ (prefixWord ++ tailWord_5456263).sum := by decide
  have hdescent : baseEnd_5456263 < baseStart_5456263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456317 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_5456317 : Nat := 118140960795 + 5456317 * 2 ^ 59
def prefixEnd_5456317 : Nat := 4983230072969 + 3 ^ 40 * 5456317 * 2
def baseEnd_5456317 : Nat := 2801713224298233868344361

theorem tailTrace_5456317 : CollatzResearch.WordTrace tailWord_5456317 prefixEnd_5456317 2801713224298233868344361 := by
  unfold tailWord_5456317
  simp only [CollatzResearch.WordTrace]
  refine ⟨199008230173702848599167205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132672153449135232399444803 199008230173702848599167205)
  ·
    refine ⟨37314043157569284112343851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199008230173702848599167205 37314043157569284112343851)
    ·
      refine ⟨55971064736353926168515777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37314043157569284112343851 55971064736353926168515777)
      ·
        refine ⟨41978298552265444626386833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55971064736353926168515777 41978298552265444626386833)
        ·
          refine ⟨31483723914199083469790125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41978298552265444626386833 31483723914199083469790125)
          ·
            refine ⟨11806396467824656301171297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31483723914199083469790125 11806396467824656301171297)
            ·
              refine ⟨8854797350868492225878473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11806396467824656301171297 8854797350868492225878473)
              ·
                refine ⟨6641098013151369169408855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8854797350868492225878473 6641098013151369169408855)
                ·
                  refine ⟨9961647019727053754113283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6641098013151369169408855 9961647019727053754113283)
                  ·
                    refine ⟨14942470529590580631169925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9961647019727053754113283 14942470529590580631169925)
                    ·
                      refine ⟨2801713224298233868344361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14942470529590580631169925 2801713224298233868344361)
                      ·
                        rfl

theorem cell23_5456317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_5456317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456317 prefixEnd_5456317 := by exact prefixLift 5456317
  have htrace : WordTrace (prefixWord ++ tailWord_5456317) baseStart_5456317 baseEnd_5456317 := by
    simpa [prefixWord, tailWord_5456317, baseEnd_5456317] using wordTrace_append hprefix tailTrace_5456317
  have hstable : (prefixWord ++ tailWord_5456317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456317).length < 2 ^ (prefixWord ++ tailWord_5456317).sum := by decide
  have hdescent : baseEnd_5456317 < baseStart_5456317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456340 : List Nat := [2, 4, 1, 2, 2, 3, 9]
def baseStart_5456340 : Nat := 118140960795 + 5456340 * 2 ^ 59
def prefixEnd_5456340 : Nat := 4983230072969 + 3 ^ 40 * 5456340 * 2
def baseEnd_5456340 : Nat := 34589197954978855288355

theorem tailTrace_5456340 : CollatzResearch.WordTrace tailWord_5456340 prefixEnd_5456340 34589197954978855288355 := by
  unfold tailWord_5456340
  simp only [CollatzResearch.WordTrace]
  refine ⟨99504534526309761763627237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132672712701746349018169649 99504534526309761763627237)
  ·
    refine ⟨18657100223683080330680107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99504534526309761763627237 18657100223683080330680107)
    ·
      refine ⟨27985650335524620496020161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18657100223683080330680107 27985650335524620496020161)
      ·
        refine ⟨20989237751643465372015121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27985650335524620496020161 20989237751643465372015121)
        ·
          refine ⟨15741928313732599029011341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20989237751643465372015121 15741928313732599029011341)
          ·
            refine ⟨5903223117649724635879253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15741928313732599029011341 5903223117649724635879253)
            ·
              refine ⟨34589197954978855288355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5903223117649724635879253 34589197954978855288355)
              ·
                rfl

theorem cell23_5456340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 9].length) (baseStart_5456340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456340 prefixEnd_5456340 := by exact prefixLift 5456340
  have htrace : WordTrace (prefixWord ++ tailWord_5456340) baseStart_5456340 baseEnd_5456340 := by
    simpa [prefixWord, tailWord_5456340, baseEnd_5456340] using wordTrace_append hprefix tailTrace_5456340
  have hstable : (prefixWord ++ tailWord_5456340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456340).length < 2 ^ (prefixWord ++ tailWord_5456340).sum := by decide
  have hdescent : baseEnd_5456340 < baseStart_5456340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456353 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 2, 7]
def baseStart_5456353 : Nat := 118140960795 + 5456353 * 2 ^ 59
def prefixEnd_5456353 : Nat := 4983230072969 + 3 ^ 40 * 5456353 * 2
def baseEnd_5456353 : Nat := 933910569867265242498065

theorem tailTrace_5456353 : CollatzResearch.WordTrace tailWord_5456353 prefixEnd_5456353 933910569867265242498065 := by
  unfold tailWord_5456353
  simp only [CollatzResearch.WordTrace]
  refine ⟨199009543201572426747477713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132673028801048284498318475 199009543201572426747477713)
  ·
    refine ⟨149257157401179320060608285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199009543201572426747477713 149257157401179320060608285)
    ·
      refine ⟨55971434025442245022728107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149257157401179320060608285 55971434025442245022728107)
      ·
        refine ⟨83957151038163367534092161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55971434025442245022728107 83957151038163367534092161)
        ·
          refine ⟨62967863278622525650569121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83957151038163367534092161 62967863278622525650569121)
          ·
            refine ⟨47225897458966894237926841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62967863278622525650569121 47225897458966894237926841)
            ·
              refine ⟨35419423094225170678445131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47225897458966894237926841 35419423094225170678445131)
              ·
                refine ⟨53129134641337756017667697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35419423094225170678445131 53129134641337756017667697)
                ·
                  refine ⟨39846850981003317013250773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53129134641337756017667697 39846850981003317013250773)
                  ·
                    refine ⟨933910569867265242498065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39846850981003317013250773 933910569867265242498065)
                    ·
                      rfl

theorem cell23_5456353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_5456353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456353 prefixEnd_5456353 := by exact prefixLift 5456353
  have htrace : WordTrace (prefixWord ++ tailWord_5456353) baseStart_5456353 baseEnd_5456353 := by
    simpa [prefixWord, tailWord_5456353, baseEnd_5456353] using wordTrace_append hprefix tailTrace_5456353
  have hstable : (prefixWord ++ tailWord_5456353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456353).length < 2 ^ (prefixWord ++ tailWord_5456353).sum := by decide
  have hdescent : baseEnd_5456353 < baseStart_5456353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456393 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_5456393 : Nat := 118140960795 + 5456393 * 2 ^ 59
def prefixEnd_5456393 : Nat := 4983230072969 + 3 ^ 40 * 5456393 * 2
def baseEnd_5456393 : Nat := 2801752248827975570994011

theorem tailTrace_5456393 : CollatzResearch.WordTrace tailWord_5456393 prefixEnd_5456393 2801752248827975570994011 := by
  unfold tailWord_5456393
  simp only [CollatzResearch.WordTrace]
  refine ⟨199011002121427513578933833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132674001414285009052622555 199011002121427513578933833)
  ·
    refine ⟨149258251591070635184200375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199011002121427513578933833 149258251591070635184200375)
    ·
      refine ⟨223887377386605952776300563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149258251591070635184200375 223887377386605952776300563)
      ·
        refine ⟨335831066079908929164450845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223887377386605952776300563 335831066079908929164450845)
        ·
          refine ⟨125936649779965848436669067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335831066079908929164450845 125936649779965848436669067)
          ·
            refine ⟨188904974669948772655003601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125936649779965848436669067 188904974669948772655003601)
            ·
              refine ⟨141678731002461579491252701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188904974669948772655003601 141678731002461579491252701)
              ·
                refine ⟨53129524125923092309219763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141678731002461579491252701 53129524125923092309219763)
                ·
                  refine ⟨79694286188884638463829645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53129524125923092309219763 79694286188884638463829645)
                  ·
                    refine ⟨29885357320831739423936117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79694286188884638463829645 29885357320831739423936117)
                    ·
                      refine ⟨2801752248827975570994011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29885357320831739423936117 2801752248827975570994011)
                      ·
                        rfl

theorem cell23_5456393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_5456393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456393 prefixEnd_5456393 := by exact prefixLift 5456393
  have htrace : WordTrace (prefixWord ++ tailWord_5456393) baseStart_5456393 baseEnd_5456393 := by
    simpa [prefixWord, tailWord_5456393, baseEnd_5456393] using wordTrace_append hprefix tailTrace_5456393
  have hstable : (prefixWord ++ tailWord_5456393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456393).length < 2 ^ (prefixWord ++ tailWord_5456393).sum := by decide
  have hdescent : baseEnd_5456393 < baseStart_5456393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456410 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_5456410 : Nat := 118140960795 + 5456410 * 2 ^ 59
def prefixEnd_5456410 : Nat := 4983230072969 + 3 ^ 40 * 5456410 * 2
def baseEnd_5456410 : Nat := 2801760977999102004481433

theorem tailTrace_5456410 : CollatzResearch.WordTrace tailWord_5456410 prefixEnd_5456410 2801760977999102004481433 := by
  unfold tailWord_5456410
  simp only [CollatzResearch.WordTrace]
  refine ⟨49752905540591481370575671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132674414774910616988201789 49752905540591481370575671)
  ·
    refine ⟨74629358310887222055863507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49752905540591481370575671 74629358310887222055863507)
    ·
      refine ⟨111944037466330833083795261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74629358310887222055863507 111944037466330833083795261)
      ·
        refine ⟨41979014049874062406423223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111944037466330833083795261 41979014049874062406423223)
        ·
          refine ⟨62968521074811093609634835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41979014049874062406423223 62968521074811093609634835)
          ·
            refine ⟨94452781612216640414452253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62968521074811093609634835 94452781612216640414452253)
            ·
              refine ⟨35419793104581240155419595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94452781612216640414452253 35419793104581240155419595)
              ·
                refine ⟨53129689656871860233129393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35419793104581240155419595 53129689656871860233129393)
                ·
                  refine ⟨39847267242653895174847045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53129689656871860233129393 39847267242653895174847045)
                  ·
                    refine ⟨7471362607997605345283821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39847267242653895174847045 7471362607997605345283821)
                    ·
                      refine ⟨2801760977999102004481433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7471362607997605345283821 2801760977999102004481433)
                      ·
                        rfl

theorem cell23_5456410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_5456410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456410 prefixEnd_5456410 := by exact prefixLift 5456410
  have htrace : WordTrace (prefixWord ++ tailWord_5456410) baseStart_5456410 baseEnd_5456410 := by
    simpa [prefixWord, tailWord_5456410, baseEnd_5456410] using wordTrace_append hprefix tailTrace_5456410
  have hstable : (prefixWord ++ tailWord_5456410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456410).length < 2 ^ (prefixWord ++ tailWord_5456410).sum := by decide
  have hdescent : baseEnd_5456410 < baseStart_5456410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456424 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5456424 : Nat := 118140960795 + 5456424 * 2 ^ 59
def prefixEnd_5456424 : Nat := 4983230072969 + 3 ^ 40 * 5456424 * 2
def baseEnd_5456424 : Nat := 2801768166728264949706369

theorem tailTrace_5456424 : CollatzResearch.WordTrace tailWord_5456424 prefixEnd_5456424 2801768166728264949706369 := by
  unfold tailWord_5456424
  simp only [CollatzResearch.WordTrace]
  refine ⟨99506066392157602936656163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132674755189543470582208217 99506066392157602936656163)
  ·
    refine ⟨149259099588236404404984245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99506066392157602936656163 149259099588236404404984245)
    ·
      refine ⟨13993040586397162912967273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149259099588236404404984245 13993040586397162912967273)
      ·
        refine ⟨10494780439797872184725455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13993040586397162912967273 10494780439797872184725455)
        ·
          refine ⟨15742170659696808277088183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10494780439797872184725455 15742170659696808277088183)
          ·
            refine ⟨23613255989545212415632275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15742170659696808277088183 23613255989545212415632275)
            ·
              refine ⟨35419883984317818623448413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23613255989545212415632275 35419883984317818623448413)
              ·
                refine ⟨13282456494119181983793155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35419883984317818623448413 13282456494119181983793155)
                ·
                  refine ⟨19923684741178772975689733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13282456494119181983793155 19923684741178772975689733)
                  ·
                    refine ⟨3735690888971019932941825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19923684741178772975689733 3735690888971019932941825)
                    ·
                      refine ⟨2801768166728264949706369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3735690888971019932941825 2801768166728264949706369)
                      ·
                        rfl

theorem cell23_5456424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5456424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456424 prefixEnd_5456424 := by exact prefixLift 5456424
  have htrace : WordTrace (prefixWord ++ tailWord_5456424) baseStart_5456424 baseEnd_5456424 := by
    simpa [prefixWord, tailWord_5456424, baseEnd_5456424] using wordTrace_append hprefix tailTrace_5456424
  have hstable : (prefixWord ++ tailWord_5456424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456424).length < 2 ^ (prefixWord ++ tailWord_5456424).sum := by decide
  have hdescent : baseEnd_5456424 < baseStart_5456424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456440 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_5456440 : Nat := 118140960795 + 5456440 * 2 ^ 59
def prefixEnd_5456440 : Nat := 4983230072969 + 3 ^ 40 * 5456440 * 2
def baseEnd_5456440 : Nat := 2801776382418736887106295

theorem tailTrace_5456440 : CollatzResearch.WordTrace tailWord_5456440 prefixEnd_5456440 2801776382418736887106295 := by
  unfold tailWord_5456440
  simp only [CollatzResearch.WordTrace]
  refine ⟨99506358176128620302947387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132675144234838160403929849 99506358176128620302947387)
  ·
    refine ⟨149259537264192930454421081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99506358176128620302947387 149259537264192930454421081)
    ·
      refine ⟨111944652948144697840815811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149259537264192930454421081 111944652948144697840815811)
      ·
        refine ⟨167916979422217046761223717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111944652948144697840815811 167916979422217046761223717)
        ·
          refine ⟨31484433641665696267729447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167916979422217046761223717 31484433641665696267729447)
          ·
            refine ⟨47226650462498544401594171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31484433641665696267729447 47226650462498544401594171)
            ·
              refine ⟨70839975693747816602391257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47226650462498544401594171 70839975693747816602391257)
              ·
                refine ⟨53129981770310862451793443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70839975693747816602391257 53129981770310862451793443)
                ·
                  refine ⟨79694972655466293677690165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53129981770310862451793443 79694972655466293677690165)
                  ·
                    refine ⟨7471403686449965032283453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79694972655466293677690165 7471403686449965032283453)
                    ·
                      refine ⟨2801776382418736887106295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7471403686449965032283453 2801776382418736887106295)
                      ·
                        rfl

theorem cell23_5456440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_5456440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456440 prefixEnd_5456440 := by exact prefixLift 5456440
  have htrace : WordTrace (prefixWord ++ tailWord_5456440) baseStart_5456440 baseEnd_5456440 := by
    simpa [prefixWord, tailWord_5456440, baseEnd_5456440] using wordTrace_append hprefix tailTrace_5456440
  have hstable : (prefixWord ++ tailWord_5456440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456440).length < 2 ^ (prefixWord ++ tailWord_5456440).sum := by decide
  have hdescent : baseEnd_5456440 < baseStart_5456440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456447 : List Nat := [1, 1, 2, 2, 3, 2, 4, 3, 5]
def baseStart_5456447 : Nat := 118140960795 + 5456447 * 2 ^ 59
def prefixEnd_5456447 : Nat := 4983230072969 + 3 ^ 40 * 5456447 * 2
def baseEnd_5456447 : Nat := 311308886309257595524307

theorem tailTrace_5456447 : CollatzResearch.WordTrace tailWord_5456447 prefixEnd_5456447 311308886309257595524307 := by
  unfold tailWord_5456447
  simp only [CollatzResearch.WordTrace]
  refine ⟨199012971663231880801399595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132675314442154587200933063 199012971663231880801399595)
  ·
    refine ⟨298519457494847821202099393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199012971663231880801399595 298519457494847821202099393)
    ·
      refine ⟨223889593121135865901574545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298519457494847821202099393 223889593121135865901574545)
      ·
        refine ⟨167917194840851899426180909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223889593121135865901574545 167917194840851899426180909)
        ·
          refine ⟨62968948065319462284817841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167917194840851899426180909 62968948065319462284817841)
          ·
            refine ⟨47226711048989596713613381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62968948065319462284817841 47226711048989596713613381)
            ·
              refine ⟨8855008321685549383802509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47226711048989596713613381 8855008321685549383802509)
              ·
                refine ⟨3320628120632081018925941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8855008321685549383802509 3320628120632081018925941)
                ·
                  refine ⟨311308886309257595524307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3320628120632081018925941 311308886309257595524307)
                  ·
                    rfl

theorem cell23_5456447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 5].length) (baseStart_5456447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456447 prefixEnd_5456447 := by exact prefixLift 5456447
  have htrace : WordTrace (prefixWord ++ tailWord_5456447) baseStart_5456447 baseEnd_5456447 := by
    simpa [prefixWord, tailWord_5456447, baseEnd_5456447] using wordTrace_append hprefix tailTrace_5456447
  have hstable : (prefixWord ++ tailWord_5456447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456447).length < 2 ^ (prefixWord ++ tailWord_5456447).sum := by decide
  have hdescent : baseEnd_5456447 < baseStart_5456447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456452 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5456452 : Nat := 118140960795 + 5456452 * 2 ^ 59
def prefixEnd_5456452 : Nat := 4983230072969 + 3 ^ 40 * 5456452 * 2
def baseEnd_5456452 : Nat := 2801782544186590840156241

theorem tailTrace_5456452 : CollatzResearch.WordTrace tailWord_5456452 prefixEnd_5456452 2801782544186590840156241 := by
  unfold tailWord_5456452
  simp only [CollatzResearch.WordTrace]
  refine ⟨99506577014106883327665805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132675436018809177770221073 99506577014106883327665805)
  ·
    refine ⟨37314966380290081247874677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99506577014106883327665805 37314966380290081247874677)
    ·
      refine ⟨3498278098152195116988251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37314966380290081247874677 3498278098152195116988251)
      ·
        refine ⟨5247417147228292675482377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3498278098152195116988251 5247417147228292675482377)
        ·
          refine ⟨3935562860421219506611783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5247417147228292675482377 3935562860421219506611783)
          ·
            refine ⟨5903344290631829259917675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935562860421219506611783 5903344290631829259917675)
            ·
              refine ⟨8855016435947743889876513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5903344290631829259917675 8855016435947743889876513)
              ·
                refine ⟨6641262326960807917407385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8855016435947743889876513 6641262326960807917407385)
                ·
                  refine ⟨4980946745220605938055539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6641262326960807917407385 4980946745220605938055539)
                  ·
                    refine ⟨7471420117830908907083309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4980946745220605938055539 7471420117830908907083309)
                    ·
                      refine ⟨2801782544186590840156241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7471420117830908907083309 2801782544186590840156241)
                      ·
                        rfl

theorem cell23_5456452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5456452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456452 prefixEnd_5456452 := by exact prefixLift 5456452
  have htrace : WordTrace (prefixWord ++ tailWord_5456452) baseStart_5456452 baseEnd_5456452 := by
    simpa [prefixWord, tailWord_5456452, baseEnd_5456452] using wordTrace_append hprefix tailTrace_5456452
  have hstable : (prefixWord ++ tailWord_5456452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456452).length < 2 ^ (prefixWord ++ tailWord_5456452).sum := by decide
  have hdescent : baseEnd_5456452 < baseStart_5456452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456454 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5456454 : Nat := 118140960795 + 5456454 * 2 ^ 59
def prefixEnd_5456454 : Nat := 4983230072969 + 3 ^ 40 * 5456454 * 2
def baseEnd_5456454 : Nat := 2801783571147899832331231

theorem tailTrace_5456454 : CollatzResearch.WordTrace tailWord_5456454 prefixEnd_5456454 2801783571147899832331231 := by
  unfold tailWord_5456454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6219163342943953781153263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132675484649471013997936277 6219163342943953781153263)
  ·
    refine ⟨9328745014415930671729895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6219163342943953781153263 9328745014415930671729895)
    ·
      refine ⟨13993117521623896007594843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9328745014415930671729895 13993117521623896007594843)
      ·
        refine ⟨20989676282435844011392265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13993117521623896007594843 20989676282435844011392265)
        ·
          refine ⟨15742257211826883008544199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20989676282435844011392265 15742257211826883008544199)
          ·
            refine ⟨23613385817740324512816299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15742257211826883008544199 23613385817740324512816299)
            ·
              refine ⟨35420078726610486769224449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23613385817740324512816299 35420078726610486769224449)
              ·
                refine ⟨26565059044957865076918337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35420078726610486769224449 26565059044957865076918337)
                ·
                  refine ⟨19923794283718398807688753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26565059044957865076918337 19923794283718398807688753)
                  ·
                    refine ⟨14942845712788799105766565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19923794283718398807688753 14942845712788799105766565)
                    ·
                      refine ⟨2801783571147899832331231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14942845712788799105766565 2801783571147899832331231)
                      ·
                        rfl

theorem cell23_5456454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5456454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456454 prefixEnd_5456454 := by exact prefixLift 5456454
  have htrace : WordTrace (prefixWord ++ tailWord_5456454) baseStart_5456454 baseEnd_5456454 := by
    simpa [prefixWord, tailWord_5456454, baseEnd_5456454] using wordTrace_append hprefix tailTrace_5456454
  have hstable : (prefixWord ++ tailWord_5456454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456454).length < 2 ^ (prefixWord ++ tailWord_5456454).sum := by decide
  have hdescent : baseEnd_5456454 < baseStart_5456454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456460 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_5456460 : Nat := 118140960795 + 5456460 * 2 ^ 59
def prefixEnd_5456460 : Nat := 4983230072969 + 3 ^ 40 * 5456460 * 2
def baseEnd_5456460 : Nat := 933928884010608936285401

theorem tailTrace_5456460 : CollatzResearch.WordTrace tailWord_5456460 prefixEnd_5456460 933928884010608936285401 := by
  unfold tailWord_5456460
  simp only [CollatzResearch.WordTrace]
  refine ⟨99506722906092392010811417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132675630541456522681081889 99506722906092392010811417)
  ·
    refine ⟨74630042179569294008108563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99506722906092392010811417 74630042179569294008108563)
    ·
      refine ⟨111945063269353941012162845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74630042179569294008108563 111945063269353941012162845)
      ·
        refine ⟨41979398726007727879561067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111945063269353941012162845 41979398726007727879561067)
        ·
          refine ⟨62969098089011591819341601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41979398726007727879561067 62969098089011591819341601)
          ·
            refine ⟨47226823566758693864506201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62969098089011591819341601 47226823566758693864506201)
            ·
              refine ⟨35420117675069020398379651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47226823566758693864506201 35420117675069020398379651)
              ·
                refine ⟨53130176512603530597569477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35420117675069020398379651 53130176512603530597569477)
                ·
                  refine ⟨9961908096113161987044277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53130176512603530597569477 9961908096113161987044277)
                  ·
                    refine ⟨933928884010608936285401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9961908096113161987044277 933928884010608936285401)
                    ·
                      rfl

theorem cell23_5456460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_5456460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456460 prefixEnd_5456460 := by exact prefixLift 5456460
  have htrace : WordTrace (prefixWord ++ tailWord_5456460) baseStart_5456460 baseEnd_5456460 := by
    simpa [prefixWord, tailWord_5456460, baseEnd_5456460] using wordTrace_append hprefix tailTrace_5456460
  have hstable : (prefixWord ++ tailWord_5456460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456460).length < 2 ^ (prefixWord ++ tailWord_5456460).sum := by decide
  have hdescent : baseEnd_5456460 < baseStart_5456460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456480 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_5456480 : Nat := 118140960795 + 5456480 * 2 ^ 59
def prefixEnd_5456480 : Nat := 4983230072969 + 3 ^ 40 * 5456480 * 2
def baseEnd_5456480 : Nat := 2801796921644916730606111

theorem tailTrace_5456480 : CollatzResearch.WordTrace tailWord_5456480 prefixEnd_5456480 2801796921644916730606111 := by
  unfold tailWord_5456480
  simp only [CollatzResearch.WordTrace]
  refine ⟨99507087636056163718675447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132676116848074884958233929 99507087636056163718675447)
  ·
    refine ⟨149260631454084245578013171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99507087636056163718675447 149260631454084245578013171)
    ·
      refine ⟨223890947181126368367019757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149260631454084245578013171 223890947181126368367019757)
      ·
        refine ⟨83959105192922388137632409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223890947181126368367019757 83959105192922388137632409)
        ·
          refine ⟨62969328894691791103224307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83959105192922388137632409 62969328894691791103224307)
          ·
            refine ⟨94453993342037686654836461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62969328894691791103224307 94453993342037686654836461)
            ·
              refine ⟨35420247503264132495563673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94453993342037686654836461 35420247503264132495563673)
              ·
                refine ⟨26565185627448099371672755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35420247503264132495563673 26565185627448099371672755)
                ·
                  refine ⟨39847778441172149057509133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26565185627448099371672755 39847778441172149057509133)
                  ·
                    refine ⟨14942916915439555896565925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39847778441172149057509133 14942916915439555896565925)
                    ·
                      refine ⟨2801796921644916730606111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14942916915439555896565925 2801796921644916730606111)
                      ·
                        rfl

theorem cell23_5456480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_5456480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456480 prefixEnd_5456480 := by exact prefixLift 5456480
  have htrace : WordTrace (prefixWord ++ tailWord_5456480) baseStart_5456480 baseEnd_5456480 := by
    simpa [prefixWord, tailWord_5456480, baseEnd_5456480] using wordTrace_append hprefix tailTrace_5456480
  have hstable : (prefixWord ++ tailWord_5456480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456480).length < 2 ^ (prefixWord ++ tailWord_5456480).sum := by decide
  have hdescent : baseEnd_5456480 < baseStart_5456480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456490 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_5456490 : Nat := 118140960795 + 5456490 * 2 ^ 59
def prefixEnd_5456490 : Nat := 4983230072969 + 3 ^ 40 * 5456490 * 2
def baseEnd_5456490 : Nat := 933934018817153897160355

theorem tailTrace_5456490 : CollatzResearch.WordTrace tailWord_5456490 prefixEnd_5456490 933934018817153897160355 := by
  unfold tailWord_5456490
  simp only [CollatzResearch.WordTrace]
  refine ⟨49753635000519024786303731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132676360001384066096809949 49753635000519024786303731)
  ·
    refine ⟨74630452500778537179455597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49753635000519024786303731 74630452500778537179455597)
    ·
      refine ⟨27986419687791951442295849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74630452500778537179455597 27986419687791951442295849)
      ·
        refine ⟨20989814765843963581721887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27986419687791951442295849 20989814765843963581721887)
        ·
          refine ⟨31484722148765945372582831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20989814765843963581721887 31484722148765945372582831)
          ·
            refine ⟨47227083223148918058874247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31484722148765945372582831 47227083223148918058874247)
            ·
              refine ⟨70840624834723377088311371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47227083223148918058874247 70840624834723377088311371)
              ·
                refine ⟨106260937252085065632467057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70840624834723377088311371 106260937252085065632467057)
                ·
                  refine ⟨79695702939063799224350293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106260937252085065632467057 79695702939063799224350293)
                  ·
                    refine ⟨933934018817153897160355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79695702939063799224350293 933934018817153897160355)
                    ·
                      rfl

theorem cell23_5456490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_5456490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456490 prefixEnd_5456490 := by exact prefixLift 5456490
  have htrace : WordTrace (prefixWord ++ tailWord_5456490) baseStart_5456490 baseEnd_5456490 := by
    simpa [prefixWord, tailWord_5456490, baseEnd_5456490] using wordTrace_append hprefix tailTrace_5456490
  have hstable : (prefixWord ++ tailWord_5456490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456490).length < 2 ^ (prefixWord ++ tailWord_5456490).sum := by decide
  have hdescent : baseEnd_5456490 < baseStart_5456490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456517 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_5456517 : Nat := 118140960795 + 5456517 * 2 ^ 59
def prefixEnd_5456517 : Nat := 4983230072969 + 3 ^ 40 * 5456517 * 2
def baseEnd_5456517 : Nat := 2801815920429133085843441

theorem tailTrace_5456517 : CollatzResearch.WordTrace tailWord_5456517 prefixEnd_5456517 2801815920429133085843441 := by
  unfold tailWord_5456517
  simp only [CollatzResearch.WordTrace]
  refine ⟨199015524772978282756447805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132677016515318855170965203 199015524772978282756447805)
  ·
    refine ⟨74630821789866856033667927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199015524772978282756447805 74630821789866856033667927)
    ·
      refine ⟨111946232684800284050501891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74630821789866856033667927 111946232684800284050501891)
      ·
        refine ⟨167919349027200426075752837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111946232684800284050501891 167919349027200426075752837)
        ·
          refine ⟨31484877942600079889203657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167919349027200426075752837 31484877942600079889203657)
          ·
            refine ⟨23613658456950059916902743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31484877942600079889203657 23613658456950059916902743)
            ·
              refine ⟨35420487685425089875354115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23613658456950059916902743 35420487685425089875354115)
              ·
                refine ⟨53130731528137634813031173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35420487685425089875354115 53130731528137634813031173)
                ·
                  refine ⟨9962012161525806527443345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53130731528137634813031173 9962012161525806527443345)
                  ·
                    refine ⟨7471509121144354895582509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9962012161525806527443345 7471509121144354895582509)
                    ·
                      refine ⟨2801815920429133085843441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7471509121144354895582509 2801815920429133085843441)
                      ·
                        rfl

theorem cell23_5456517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_5456517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456517 prefixEnd_5456517 := by exact prefixLift 5456517
  have htrace : WordTrace (prefixWord ++ tailWord_5456517) baseStart_5456517 baseEnd_5456517 := by
    simpa [prefixWord, tailWord_5456517, baseEnd_5456517] using wordTrace_append hprefix tailTrace_5456517
  have hstable : (prefixWord ++ tailWord_5456517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456517).length < 2 ^ (prefixWord ++ tailWord_5456517).sum := by decide
  have hdescent : baseEnd_5456517 < baseStart_5456517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456587 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 4, 6, 2]
def baseStart_5456587 : Nat := 118140960795 + 5456587 * 2 ^ 59
def prefixEnd_5456587 : Nat := 4983230072969 + 3 ^ 40 * 5456587 * 2
def baseEnd_5456587 : Nat := 2801851864074947811968119

theorem tailTrace_5456587 : CollatzResearch.WordTrace tailWord_5456587 prefixEnd_5456587 2801851864074947811968119 := by
  unfold tailWord_5456587
  simp only [CollatzResearch.WordTrace]
  refine ⟨199018077882724684711496015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132678718588483123140997343 199018077882724684711496015)
  ·
    refine ⟨298527116824087027067244023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199018077882724684711496015 298527116824087027067244023)
    ·
      refine ⟨447790675236130540600866035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298527116824087027067244023 447790675236130540600866035)
      ·
        refine ⟨671686012854195810901299053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447790675236130540600866035 671686012854195810901299053)
        ·
          refine ⟨251882254820323429087987145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 671686012854195810901299053 251882254820323429087987145)
          ·
            refine ⟨188911691115242571815990359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251882254820323429087987145 188911691115242571815990359)
            ·
              refine ⟨283367536672863857723985539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188911691115242571815990359 283367536672863857723985539)
              ·
                refine ⟨425051305009295786585978309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283367536672863857723985539 425051305009295786585978309)
                ·
                  refine ⟨79697119689242959984870933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425051305009295786585978309 79697119689242959984870933)
                  ·
                    refine ⟨3735802485433263749290825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79697119689242959984870933 3735802485433263749290825)
                    ·
                      refine ⟨2801851864074947811968119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3735802485433263749290825 2801851864074947811968119)
                      ·
                        rfl

theorem cell23_5456587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 6, 2].length) (baseStart_5456587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456587 prefixEnd_5456587 := by exact prefixLift 5456587
  have htrace : WordTrace (prefixWord ++ tailWord_5456587) baseStart_5456587 baseEnd_5456587 := by
    simpa [prefixWord, tailWord_5456587, baseEnd_5456587] using wordTrace_append hprefix tailTrace_5456587
  have hstable : (prefixWord ++ tailWord_5456587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456587).length < 2 ^ (prefixWord ++ tailWord_5456587).sum := by decide
  have hdescent : baseEnd_5456587 < baseStart_5456587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456617 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_5456617 : Nat := 118140960795 + 5456617 * 2 ^ 59
def prefixEnd_5456617 : Nat := 4983230072969 + 3 ^ 40 * 5456617 * 2
def baseEnd_5456617 : Nat := 2801867268494582694592981

theorem tailTrace_5456617 : CollatzResearch.WordTrace tailWord_5456617 prefixEnd_5456617 2801867268494582694592981 := by
  unfold tailWord_5456617
  simp only [CollatzResearch.WordTrace]
  refine ⟨199019172072615999835088105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132679448048410666556725403 199019172072615999835088105)
  ·
    refine ⟨149264379054461999876316079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199019172072615999835088105 149264379054461999876316079)
    ·
      refine ⟨223896568581692999814474119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149264379054461999876316079 223896568581692999814474119)
      ·
        refine ⟨335844852872539499721711179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223896568581692999814474119 335844852872539499721711179)
        ·
          refine ⟨503767279308809249582566769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335844852872539499721711179 503767279308809249582566769)
          ·
            refine ⟨377825459481606937186925077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503767279308809249582566769 377825459481606937186925077)
            ·
              refine ⟨17710568413200325180637113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 377825459481606937186925077 17710568413200325180637113)
              ·
                refine ⟨13282926309900243885477835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17710568413200325180637113 13282926309900243885477835)
                ·
                  refine ⟨19924389464850365828216753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13282926309900243885477835 19924389464850365828216753)
                  ·
                    refine ⟨14943292098637774371162565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19924389464850365828216753 14943292098637774371162565)
                    ·
                      refine ⟨2801867268494582694592981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14943292098637774371162565 2801867268494582694592981)
                      ·
                        rfl

theorem cell23_5456617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_5456617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456617 prefixEnd_5456617 := by exact prefixLift 5456617
  have htrace : WordTrace (prefixWord ++ tailWord_5456617) baseStart_5456617 baseEnd_5456617 := by
    simpa [prefixWord, tailWord_5456617, baseEnd_5456617] using wordTrace_append hprefix tailTrace_5456617
  have hstable : (prefixWord ++ tailWord_5456617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456617).length < 2 ^ (prefixWord ++ tailWord_5456617).sum := by decide
  have hdescent : baseEnd_5456617 < baseStart_5456617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456621 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_5456621 : Nat := 118140960795 + 5456621 * 2 ^ 59
def prefixEnd_5456621 : Nat := 4983230072969 + 3 ^ 40 * 5456621 * 2
def baseEnd_5456621 : Nat := 2801869322417200678942963

theorem tailTrace_5456621 : CollatzResearch.WordTrace tailWord_5456621 prefixEnd_5456621 2801869322417200678942963 := by
  unfold tailWord_5456621
  simp only [CollatzResearch.WordTrace]
  refine ⟨199019317964601508518233717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132679545309734339012155811 199019317964601508518233717)
  ·
    refine ⟨18658061059181391423584411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199019317964601508518233717 18658061059181391423584411)
    ·
      refine ⟨27987091588772087135376617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18658061059181391423584411 27987091588772087135376617)
      ·
        refine ⟨20990318691579065351532463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27987091588772087135376617 20990318691579065351532463)
        ·
          refine ⟨31485478037368598027298695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20990318691579065351532463 31485478037368598027298695)
          ·
            refine ⟨47228217056052897040948043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31485478037368598027298695 47228217056052897040948043)
            ·
              refine ⟨70842325584079345561422065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47228217056052897040948043 70842325584079345561422065)
              ·
                refine ⟨53131744188059509171066549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70842325584079345561422065 53131744188059509171066549)
                ·
                  refine ⟨4981101017630578984787489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53131744188059509171066549 4981101017630578984787489)
                  ·
                    refine ⟨3735825763222934238590617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4981101017630578984787489 3735825763222934238590617)
                    ·
                      refine ⟨2801869322417200678942963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3735825763222934238590617 2801869322417200678942963)
                      ·
                        rfl

theorem cell23_5456621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_5456621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456621 prefixEnd_5456621 := by exact prefixLift 5456621
  have htrace : WordTrace (prefixWord ++ tailWord_5456621) baseStart_5456621 baseEnd_5456621 := by
    simpa [prefixWord, tailWord_5456621, baseEnd_5456621] using wordTrace_append hprefix tailTrace_5456621
  have hstable : (prefixWord ++ tailWord_5456621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456621).length < 2 ^ (prefixWord ++ tailWord_5456621).sum := by decide
  have hdescent : baseEnd_5456621 < baseStart_5456621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456624 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 3]
def baseStart_5456624 : Nat := 118140960795 + 5456624 * 2 ^ 59
def prefixEnd_5456624 : Nat := 4983230072969 + 3 ^ 40 * 5456624 * 2
def baseEnd_5456624 : Nat := 2801870862859164167205449

theorem tailTrace_5456624 : CollatzResearch.WordTrace tailWord_5456624 prefixEnd_5456624 2801870862859164167205449 := by
  unfold tailWord_5456624
  simp only [CollatzResearch.WordTrace]
  refine ⟨99509713691795320015296463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132679618255727093353728617 99509713691795320015296463)
  ·
    refine ⟨149264570537692980022944695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99509713691795320015296463 149264570537692980022944695)
    ·
      refine ⟨223896855806539470034417043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149264570537692980022944695 223896855806539470034417043)
      ·
        refine ⟨335845283709809205051625565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223896855806539470034417043 335845283709809205051625565)
        ·
          refine ⟨125941981391178451894359587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335845283709809205051625565 125941981391178451894359587)
          ·
            refine ⟨188912972086767677841539381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125941981391178451894359587 188912972086767677841539381)
            ·
              refine ⟨17710591133134469797644317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188912972086767677841539381 17710591133134469797644317)
              ·
                refine ⟨6641471674925426174116619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17710591133134469797644317 6641471674925426174116619)
                ·
                  refine ⟨9962207512388139261174929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6641471674925426174116619 9962207512388139261174929)
                  ·
                    refine ⟨7471655634291104445881197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9962207512388139261174929 7471655634291104445881197)
                    ·
                      refine ⟨2801870862859164167205449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7471655634291104445881197 2801870862859164167205449)
                      ·
                        rfl

theorem cell23_5456624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 3].length) (baseStart_5456624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456624 prefixEnd_5456624 := by exact prefixLift 5456624
  have htrace : WordTrace (prefixWord ++ tailWord_5456624) baseStart_5456624 baseEnd_5456624 := by
    simpa [prefixWord, tailWord_5456624, baseEnd_5456624] using wordTrace_append hprefix tailTrace_5456624
  have hstable : (prefixWord ++ tailWord_5456624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456624).length < 2 ^ (prefixWord ++ tailWord_5456624).sum := by decide
  have hdescent : baseEnd_5456624 < baseStart_5456624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456638 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_5456638 : Nat := 118140960795 + 5456638 * 2 ^ 59
def prefixEnd_5456638 : Nat := 4983230072969 + 3 ^ 40 * 5456638 * 2
def baseEnd_5456638 : Nat := 2801878051588327112430385

theorem tailTrace_5456638 : CollatzResearch.WordTrace tailWord_5456638 prefixEnd_5456638 2801878051588327112430385 := by
  unfold tailWord_5456638
  simp only [CollatzResearch.WordTrace]
  refine ⟨24877492250692490052700321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132679958670359946947735045 24877492250692490052700321)
  ·
    refine ⟨18658119188019367539525241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24877492250692490052700321 18658119188019367539525241)
    ·
      refine ⟨13993589391014525654643931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18658119188019367539525241 13993589391014525654643931)
      ·
        refine ⟨20990384086521788481965897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13993589391014525654643931 20990384086521788481965897)
        ·
          refine ⟨15742788064891341361474423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20990384086521788481965897 15742788064891341361474423)
          ·
            refine ⟨23614182097337012042211635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15742788064891341361474423 23614182097337012042211635)
            ·
              refine ⟨35421273146005518063317453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23614182097337012042211635 35421273146005518063317453)
              ·
                refine ⟨13282977429752069273744045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35421273146005518063317453 13282977429752069273744045)
                ·
                  refine ⟨4981116536157025977654017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13282977429752069273744045 4981116536157025977654017)
                  ·
                    refine ⟨3735837402117769483240513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4981116536157025977654017 3735837402117769483240513)
                    ·
                      refine ⟨2801878051588327112430385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3735837402117769483240513 2801878051588327112430385)
                      ·
                        rfl

theorem cell23_5456638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_5456638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456638 prefixEnd_5456638 := by exact prefixLift 5456638
  have htrace : WordTrace (prefixWord ++ tailWord_5456638) baseStart_5456638 baseEnd_5456638 := by
    simpa [prefixWord, tailWord_5456638, baseEnd_5456638] using wordTrace_append hprefix tailTrace_5456638
  have hstable : (prefixWord ++ tailWord_5456638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456638).length < 2 ^ (prefixWord ++ tailWord_5456638).sum := by decide
  have hdescent : baseEnd_5456638 < baseStart_5456638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456705 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5456705 : Nat := 118140960795 + 5456705 * 2 ^ 59
def prefixEnd_5456705 : Nat := 4983230072969 + 3 ^ 40 * 5456705 * 2
def baseEnd_5456705 : Nat := 2801912454792178350292577

theorem tailTrace_5456705 : CollatzResearch.WordTrace tailWord_5456705 prefixEnd_5456705 2801912454792178350292577 := by
  unfold tailWord_5456705
  simp only [CollatzResearch.WordTrace]
  refine ⟨199022381696297190864291569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132681587797531460576194379 199022381696297190864291569)
  ·
    refine ⟨149266786272222893148218677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199022381696297190864291569 149266786272222893148218677)
    ·
      refine ⟨13993761213020896232645501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149266786272222893148218677 13993761213020896232645501)
      ·
        refine ⟨5247660454882836087242063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13993761213020896232645501 5247660454882836087242063)
        ·
          refine ⟨7871490682324254130863095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5247660454882836087242063 7871490682324254130863095)
          ·
            refine ⟨11807236023486381196294643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7871490682324254130863095 11807236023486381196294643)
            ·
              refine ⟨17710854035229571794441965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11807236023486381196294643 17710854035229571794441965)
              ·
                refine ⟨6641570263211089422915737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17710854035229571794441965 6641570263211089422915737)
                ·
                  refine ⟨4981177697408317067186803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6641570263211089422915737 4981177697408317067186803)
                  ·
                    refine ⟨7471766546112475600780205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4981177697408317067186803 7471766546112475600780205)
                    ·
                      refine ⟨2801912454792178350292577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7471766546112475600780205 2801912454792178350292577)
                      ·
                        rfl

theorem cell23_5456705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5456705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456705 prefixEnd_5456705 := by exact prefixLift 5456705
  have htrace : WordTrace (prefixWord ++ tailWord_5456705) baseStart_5456705 baseEnd_5456705 := by
    simpa [prefixWord, tailWord_5456705, baseEnd_5456705] using wordTrace_append hprefix tailTrace_5456705
  have hstable : (prefixWord ++ tailWord_5456705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456705).length < 2 ^ (prefixWord ++ tailWord_5456705).sum := by decide
  have hdescent : baseEnd_5456705 < baseStart_5456705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456707 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 4]
def baseStart_5456707 : Nat := 118140960795 + 5456707 * 2 ^ 59
def prefixEnd_5456707 : Nat := 4983230072969 + 3 ^ 40 * 5456707 * 2
def baseEnd_5456707 : Nat := 2801913481753487342467567

theorem tailTrace_5456707 : CollatzResearch.WordTrace tailWord_5456707 prefixEnd_5456707 2801913481753487342467567 := by
  unfold tailWord_5456707
  simp only [CollatzResearch.WordTrace]
  refine ⟨199022454642289945205864375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132681636428193296803909583 199022454642289945205864375)
  ·
    refine ⟨298533681963434917808796563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199022454642289945205864375 298533681963434917808796563)
    ·
      refine ⟨447800522945152376713194845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298533681963434917808796563 447800522945152376713194845)
      ·
        refine ⟨167925196104432141267448067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447800522945152376713194845 167925196104432141267448067)
        ·
          refine ⟨251887794156648211901172101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167925196104432141267448067 251887794156648211901172101)
          ·
            refine ⟨47228961404371539731469769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251887794156648211901172101 47228961404371539731469769)
            ·
              refine ⟨35421721053278654798602327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47228961404371539731469769 35421721053278654798602327)
              ·
                refine ⟨53132581579917982197903491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35421721053278654798602327 53132581579917982197903491)
                ·
                  refine ⟨79698872369876973296855237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53132581579917982197903491 79698872369876973296855237)
                  ·
                    refine ⟨14943538569351932493160357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79698872369876973296855237 14943538569351932493160357)
                    ·
                      refine ⟨2801913481753487342467567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14943538569351932493160357 2801913481753487342467567)
                      ·
                        rfl

theorem cell23_5456707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_5456707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456707 prefixEnd_5456707 := by exact prefixLift 5456707
  have htrace : WordTrace (prefixWord ++ tailWord_5456707) baseStart_5456707 baseEnd_5456707 := by
    simpa [prefixWord, tailWord_5456707, baseEnd_5456707] using wordTrace_append hprefix tailTrace_5456707
  have hstable : (prefixWord ++ tailWord_5456707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456707).length < 2 ^ (prefixWord ++ tailWord_5456707).sum := by decide
  have hdescent : baseEnd_5456707 < baseStart_5456707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456787 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 5]
def baseStart_5456787 : Nat := 118140960795 + 5456787 * 2 ^ 59
def prefixEnd_5456787 : Nat := 4983230072969 + 3 ^ 40 * 5456787 * 2
def baseEnd_5456787 : Nat := 2801954560205847029467199

theorem tailTrace_5456787 : CollatzResearch.WordTrace tailWord_5456787 prefixEnd_5456787 2801954560205847029467199 := by
  unfold tailWord_5456787
  simp only [CollatzResearch.WordTrace]
  refine ⟨199025372482000118868776615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132683581654666745912517743 199025372482000118868776615)
  ·
    refine ⟨298538058723000178303164923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199025372482000118868776615 298538058723000178303164923)
    ·
      refine ⟨447807088084500267454747385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298538058723000178303164923 447807088084500267454747385)
      ·
        refine ⟨335855316063375200591060539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447807088084500267454747385 335855316063375200591060539)
        ·
          refine ⟨503782974095062800886590809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335855316063375200591060539 503782974095062800886590809)
          ·
            refine ⟨377837230571297100664943107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503782974095062800886590809 377837230571297100664943107)
            ·
              refine ⟨566755845856945650997414661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377837230571297100664943107 566755845856945650997414661)
              ·
                refine ⟨106266721098177309562015249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566755845856945650997414661 106266721098177309562015249)
                ·
                  refine ⟨79700040823632982171511437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106266721098177309562015249 79700040823632982171511437)
                  ·
                    refine ⟨29887515308862368314316789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79700040823632982171511437 29887515308862368314316789)
                    ·
                      refine ⟨2801954560205847029467199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29887515308862368314316789 2801954560205847029467199)
                      ·
                        rfl

theorem cell23_5456787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_5456787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456787 prefixEnd_5456787 := by exact prefixLift 5456787
  have htrace : WordTrace (prefixWord ++ tailWord_5456787) baseStart_5456787 baseEnd_5456787 := by
    simpa [prefixWord, tailWord_5456787, baseEnd_5456787] using wordTrace_append hprefix tailTrace_5456787
  have hstable : (prefixWord ++ tailWord_5456787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456787).length < 2 ^ (prefixWord ++ tailWord_5456787).sum := by decide
  have hdescent : baseEnd_5456787 < baseStart_5456787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456827 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 8]
def baseStart_5456827 : Nat := 118140960795 + 5456827 * 2 ^ 59
def prefixEnd_5456827 : Nat := 4983230072969 + 3 ^ 40 * 5456827 * 2
def baseEnd_5456827 : Nat := 2801975099432026872967015

theorem tailTrace_5456827 : CollatzResearch.WordTrace tailWord_5456827 prefixEnd_5456827 2801975099432026872967015 := by
  unfold tailWord_5456827
  simp only [CollatzResearch.WordTrace]
  refine ⟨199026831401855205700232735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132684554267903470466821823 199026831401855205700232735)
  ·
    refine ⟨298540247102782808550349103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199026831401855205700232735 298540247102782808550349103)
    ·
      refine ⟨447810370654174212825523655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298540247102782808550349103 447810370654174212825523655)
      ·
        refine ⟨671715555981261319238285483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447810370654174212825523655 671715555981261319238285483)
        ·
          refine ⟨1007573333971891978857428225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671715555981261319238285483 1007573333971891978857428225)
          ·
            refine ⟨755680000478918984143071169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007573333971891978857428225 755680000478918984143071169)
            ·
              refine ⟨566760000359189238107303377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755680000478918984143071169 566760000359189238107303377)
              ·
                refine ⟨425070000269391928580477533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566760000359189238107303377 425070000269391928580477533)
                ·
                  refine ⟨159401250101021973217679075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425070000269391928580477533 159401250101021973217679075)
                  ·
                    refine ⟨239101875151532959826518613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159401250101021973217679075 239101875151532959826518613)
                    ·
                      refine ⟨2801975099432026872967015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 239101875151532959826518613 2801975099432026872967015)
                      ·
                        rfl

theorem cell23_5456827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_5456827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456827 prefixEnd_5456827 := by exact prefixLift 5456827
  have htrace : WordTrace (prefixWord ++ tailWord_5456827) baseStart_5456827 baseEnd_5456827 := by
    simpa [prefixWord, tailWord_5456827, baseEnd_5456827] using wordTrace_append hprefix tailTrace_5456827
  have hstable : (prefixWord ++ tailWord_5456827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456827).length < 2 ^ (prefixWord ++ tailWord_5456827).sum := by decide
  have hdescent : baseEnd_5456827 < baseStart_5456827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456919 : List Nat := [1, 1, 3, 5, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5456919 : Nat := 118140960795 + 5456919 * 2 ^ 59
def prefixEnd_5456919 : Nat := 4983230072969 + 3 ^ 40 * 5456919 * 2
def baseEnd_5456919 : Nat := 2802022339652240513016593

theorem tailTrace_5456919 : CollatzResearch.WordTrace tailWord_5456919 prefixEnd_5456919 2802022339652240513016593 := by
  unfold tailWord_5456919
  simp only [CollatzResearch.WordTrace]
  refine ⟨199030186917521905412581811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132686791278347936941721207 199030186917521905412581811)
  ·
    refine ⟨298545280376282858118872717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199030186917521905412581811 298545280376282858118872717)
    ·
      refine ⟨111954480141106071794577269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298545280376282858118872717 111954480141106071794577269)
      ·
        refine ⟨10495732513228694230741619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111954480141106071794577269 10495732513228694230741619)
        ·
          refine ⟨15743598769843041346112429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10495732513228694230741619 15743598769843041346112429)
          ·
            refine ⟨5903849538691140504792161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15743598769843041346112429 5903849538691140504792161)
            ·
              refine ⟨4427887154018355378594121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5903849538691140504792161 4427887154018355378594121)
              ·
                refine ⟨3320915365513766533945591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4427887154018355378594121 3320915365513766533945591)
                ·
                  refine ⟨4981373048270649800918387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320915365513766533945591 4981373048270649800918387)
                  ·
                    refine ⟨7472059572405974701377581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4981373048270649800918387 7472059572405974701377581)
                    ·
                      refine ⟨2802022339652240513016593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472059572405974701377581 2802022339652240513016593)
                      ·
                        rfl

theorem cell23_5456919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5456919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456919 prefixEnd_5456919 := by exact prefixLift 5456919
  have htrace : WordTrace (prefixWord ++ tailWord_5456919) baseStart_5456919 baseEnd_5456919 := by
    simpa [prefixWord, tailWord_5456919, baseEnd_5456919] using wordTrace_append hprefix tailTrace_5456919
  have hstable : (prefixWord ++ tailWord_5456919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456919).length < 2 ^ (prefixWord ++ tailWord_5456919).sum := by decide
  have hdescent : baseEnd_5456919 < baseStart_5456919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456931 : List Nat := [1, 1, 1, 4, 3, 4, 1, 8]
def baseStart_5456931 : Nat := 118140960795 + 5456931 * 2 ^ 59
def prefixEnd_5456931 : Nat := 4983230072969 + 3 ^ 40 * 5456931 * 2
def baseEnd_5456931 : Nat := 103778833385929424669131

theorem tailTrace_5456931 : CollatzResearch.WordTrace tailWord_5456931 prefixEnd_5456931 103778833385929424669131 := by
  unfold tailWord_5456931
  simp only [CollatzResearch.WordTrace]
  refine ⟨199030624593478431462018647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132687083062318954308012431 199030624593478431462018647)
  ·
    refine ⟨298545936890217647193027971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199030624593478431462018647 298545936890217647193027971)
    ·
      refine ⟨447818905335326470789541957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298545936890217647193027971 447818905335326470789541957)
      ·
        refine ⟨83966044750373713273039117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 447818905335326470789541957 83966044750373713273039117)
        ·
          refine ⟨31487266781390142477389669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83966044750373713273039117 31487266781390142477389669)
          ·
            refine ⟨5903862521510651714510563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31487266781390142477389669 5903862521510651714510563)
            ·
              refine ⟨8855793782265977571765845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5903862521510651714510563 8855793782265977571765845)
              ·
                refine ⟨103778833385929424669131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8855793782265977571765845 103778833385929424669131)
                ·
                  rfl

theorem cell23_5456931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 8].length) (baseStart_5456931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456931 prefixEnd_5456931 := by exact prefixLift 5456931
  have htrace : WordTrace (prefixWord ++ tailWord_5456931) baseStart_5456931 baseEnd_5456931 := by
    simpa [prefixWord, tailWord_5456931, baseEnd_5456931] using wordTrace_append hprefix tailTrace_5456931
  have hstable : (prefixWord ++ tailWord_5456931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456931).length < 2 ^ (prefixWord ++ tailWord_5456931).sum := by decide
  have hdescent : baseEnd_5456931 < baseStart_5456931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456935 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 2, 4]
def baseStart_5456935 : Nat := 118140960795 + 5456935 * 2 ^ 59
def prefixEnd_5456935 : Nat := 4983230072969 + 3 ^ 40 * 5456935 * 2
def baseEnd_5456935 : Nat := 934010185114237483472173

theorem tailTrace_5456935 : CollatzResearch.WordTrace tailWord_5456935 prefixEnd_5456935 934010185114237483472173 := by
  unfold tailWord_5456935
  simp only [CollatzResearch.WordTrace]
  refine ⟨199030770485463940145164259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132687180323642626763442839 199030770485463940145164259)
  ·
    refine ⟨298546155728195910217746389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199030770485463940145164259 298546155728195910217746389)
    ·
      refine ⟨6997175524879591645728431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 298546155728195910217746389 6997175524879591645728431)
      ·
        refine ⟨10495763287319387468592647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6997175524879591645728431 10495763287319387468592647)
        ·
          refine ⟨15743644930979081202888971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10495763287319387468592647 15743644930979081202888971)
          ·
            refine ⟨23615467396468621804333457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15743644930979081202888971 23615467396468621804333457)
            ·
              refine ⟨17711600547351466353250093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23615467396468621804333457 17711600547351466353250093)
              ·
                refine ⟨6641850205256799882468785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17711600547351466353250093 6641850205256799882468785)
                ·
                  refine ⟨4981387653942599911851589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6641850205256799882468785 4981387653942599911851589)
                  ·
                    refine ⟨934010185114237483472173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4981387653942599911851589 934010185114237483472173)
                    ·
                      rfl

theorem cell23_5456935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_5456935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456935 prefixEnd_5456935 := by exact prefixLift 5456935
  have htrace : WordTrace (prefixWord ++ tailWord_5456935) baseStart_5456935 baseEnd_5456935 := by
    simpa [prefixWord, tailWord_5456935, baseEnd_5456935] using wordTrace_append hprefix tailTrace_5456935
  have hstable : (prefixWord ++ tailWord_5456935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456935).length < 2 ^ (prefixWord ++ tailWord_5456935).sum := by decide
  have hdescent : baseEnd_5456935 < baseStart_5456935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5456944 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 2, 7]
def baseStart_5456944 : Nat := 118140960795 + 5456944 * 2 ^ 59
def prefixEnd_5456944 : Nat := 4983230072969 + 3 ^ 40 * 5456944 * 2
def baseEnd_5456944 : Nat := 934011725556200971734659

theorem tailTrace_5456944 : CollatzResearch.WordTrace tailWord_5456944 prefixEnd_5456944 934011725556200971734659 := by
  unfold tailWord_5456944
  simp only [CollatzResearch.WordTrace]
  refine ⟨99515549371215667341120943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132687399161620889788161257 99515549371215667341120943)
  ·
    refine ⟨149273324056823501011681415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99515549371215667341120943 149273324056823501011681415)
    ·
      refine ⟨223909986085235251517522123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149273324056823501011681415 223909986085235251517522123)
      ·
        refine ⟨335864979127852877276283185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223909986085235251517522123 335864979127852877276283185)
        ·
          refine ⟨251898734345889657957212389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335864979127852877276283185 251898734345889657957212389)
          ·
            refine ⟨47231012689854310866977323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251898734345889657957212389 47231012689854310866977323)
            ·
              refine ⟨70846519034781466300465985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47231012689854310866977323 70846519034781466300465985)
              ·
                refine ⟨53134889276086099725349489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70846519034781466300465985 53134889276086099725349489)
                ·
                  refine ⟨39851166957064574794012117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53134889276086099725349489 39851166957064574794012117)
                  ·
                    refine ⟨934011725556200971734659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39851166957064574794012117 934011725556200971734659)
                    ·
                      rfl

theorem cell23_5456944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_5456944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5456944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5456944 prefixEnd_5456944 := by exact prefixLift 5456944
  have htrace : WordTrace (prefixWord ++ tailWord_5456944) baseStart_5456944 baseEnd_5456944 := by
    simpa [prefixWord, tailWord_5456944, baseEnd_5456944] using wordTrace_append hprefix tailTrace_5456944
  have hstable : (prefixWord ++ tailWord_5456944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5456944).length < 2 ^ (prefixWord ++ tailWord_5456944).sum := by decide
  have hdescent : baseEnd_5456944 < baseStart_5456944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5456944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457002 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_5457002 : Nat := 118140960795 + 5457002 * 2 ^ 59
def prefixEnd_5457002 : Nat := 4983230072969 + 3 ^ 40 * 5457002 * 2
def baseEnd_5457002 : Nat := 2802064958546563688278711

theorem tailTrace_5457002 : CollatzResearch.WordTrace tailWord_5457002 prefixEnd_5457002 2802064958546563688278711 := by
  unfold tailWord_5457002
  simp only [CollatzResearch.WordTrace]
  refine ⟨49758303544055302646963315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132688809450814140391902173 49758303544055302646963315)
  ·
    refine ⟨74637455316082953970444973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49758303544055302646963315 74637455316082953970444973)
    ·
      refine ⟨27989045743531107738916865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74637455316082953970444973 27989045743531107738916865)
      ·
        refine ⟨20991784307648330804187649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27989045743531107738916865 20991784307648330804187649)
        ·
          refine ⟨15743838230736248103140737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20991784307648330804187649 15743838230736248103140737)
          ·
            refine ⟨11807878673052186077355553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15743838230736248103140737 11807878673052186077355553)
            ·
              refine ⟨8855909004789139558016665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11807878673052186077355553 8855909004789139558016665)
              ·
                refine ⟨6641931753591854668512499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8855909004789139558016665 6641931753591854668512499)
                ·
                  refine ⟨9962897630387782002768749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6641931753591854668512499 9962897630387782002768749)
                  ·
                    refine ⟨3736086611395418251038281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9962897630387782002768749 3736086611395418251038281)
                    ·
                      refine ⟨2802064958546563688278711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3736086611395418251038281 2802064958546563688278711)
                      ·
                        rfl

theorem cell23_5457002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_5457002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457002 prefixEnd_5457002 := by exact prefixLift 5457002
  have htrace : WordTrace (prefixWord ++ tailWord_5457002) baseStart_5457002 baseEnd_5457002 := by
    simpa [prefixWord, tailWord_5457002, baseEnd_5457002] using wordTrace_append hprefix tailTrace_5457002
  have hstable : (prefixWord ++ tailWord_5457002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457002).length < 2 ^ (prefixWord ++ tailWord_5457002).sum := by decide
  have hdescent : baseEnd_5457002 < baseStart_5457002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457038 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_5457038 : Nat := 118140960795 + 5457038 * 2 ^ 59
def prefixEnd_5457038 : Nat := 4983230072969 + 3 ^ 40 * 5457038 * 2
def baseEnd_5457038 : Nat := 311342604872236171936505

theorem tailTrace_5457038 : CollatzResearch.WordTrace tailWord_5457038 prefixEnd_5457038 311342604872236171936505 := by
  unfold tailWord_5457038
  simp only [CollatzResearch.WordTrace]
  refine ⟨24879315900511348592020471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132689684802727192490775845 24879315900511348592020471)
  ·
    refine ⟨37318973850767022888030707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24879315900511348592020471 37318973850767022888030707)
    ·
      refine ⟨55978460776150534332046061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37318973850767022888030707 55978460776150534332046061)
      ·
        refine ⟨20991922791056450374517273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55978460776150534332046061 20991922791056450374517273)
        ·
          refine ⟨15743942093292337780887955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20991922791056450374517273 15743942093292337780887955)
          ·
            refine ⟨23615913139938506671331933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15743942093292337780887955 23615913139938506671331933)
            ·
              refine ⟨8855967427476940001749475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23615913139938506671331933 8855967427476940001749475)
              ·
                refine ⟨13283951141215410002624213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8855967427476940001749475 13283951141215410002624213)
                ·
                  refine ⟨311342604872236171936505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13283951141215410002624213 311342604872236171936505)
                  ·
                    rfl

theorem cell23_5457038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_5457038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457038 prefixEnd_5457038 := by exact prefixLift 5457038
  have htrace : WordTrace (prefixWord ++ tailWord_5457038) baseStart_5457038 baseEnd_5457038 := by
    simpa [prefixWord, tailWord_5457038, baseEnd_5457038] using wordTrace_append hprefix tailTrace_5457038
  have hstable : (prefixWord ++ tailWord_5457038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457038).length < 2 ^ (prefixWord ++ tailWord_5457038).sum := by decide
  have hdescent : baseEnd_5457038 < baseStart_5457038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457071 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_5457071 : Nat := 118140960795 + 5457071 * 2 ^ 59
def prefixEnd_5457071 : Nat := 4983230072969 + 3 ^ 40 * 5457071 * 2
def baseEnd_5457071 : Nat := 2802100388711723918315893

theorem tailTrace_5457071 : CollatzResearch.WordTrace tailWord_5457071 prefixEnd_5457071 2802100388711723918315893 := by
  unfold tailWord_5457071
  simp only [CollatzResearch.WordTrace]
  refine ⟨199035730812971235372115067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132690487208647490248076711 199035730812971235372115067)
  ·
    refine ⟨298553596219456853058172601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199035730812971235372115067 298553596219456853058172601)
    ·
      refine ⟨223915197164592639793629451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298553596219456853058172601 223915197164592639793629451)
      ·
        refine ⟨335872795746888959690444177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223915197164592639793629451 335872795746888959690444177)
        ·
          refine ⟨251904596810166719767833133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335872795746888959690444177 251904596810166719767833133)
          ·
            refine ⟨94464223803812519912937425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251904596810166719767833133 94464223803812519912937425)
            ·
              refine ⟨70848167852859389934703069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94464223803812519912937425 70848167852859389934703069)
              ·
                refine ⟨26568062944822271225513651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70848167852859389934703069 26568062944822271225513651)
                ·
                  refine ⟨39852094417233406838270477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26568062944822271225513651 39852094417233406838270477)
                  ·
                    refine ⟨14944535406462527564351429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39852094417233406838270477 14944535406462527564351429)
                    ·
                      refine ⟨2802100388711723918315893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14944535406462527564351429 2802100388711723918315893)
                      ·
                        rfl

theorem cell23_5457071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_5457071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457071 prefixEnd_5457071 := by exact prefixLift 5457071
  have htrace : WordTrace (prefixWord ++ tailWord_5457071) baseStart_5457071 baseEnd_5457071 := by
    simpa [prefixWord, tailWord_5457071, baseEnd_5457071] using wordTrace_append hprefix tailTrace_5457071
  have hstable : (prefixWord ++ tailWord_5457071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457071).length < 2 ^ (prefixWord ++ tailWord_5457071).sum := by decide
  have hdescent : baseEnd_5457071 < baseStart_5457071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
