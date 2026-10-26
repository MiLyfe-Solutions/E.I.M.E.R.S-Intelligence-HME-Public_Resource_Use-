import V185TrunkScan23Chunk1384

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8203328 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 1, 6]
def baseStart_8203328 : Nat := 118140960795 + 8203328 * 2 ^ 59
def prefixEnd_8203328 : Nat := 4983230072969 + 3 ^ 40 * 8203328 * 2
def baseEnd_8203328 : Nat := 1404083410162061891724529

theorem tailTrace_8203328 : CollatzResearch.WordTrace tailWord_8203328 prefixEnd_8203328 1404083410162061891724529 := by
  unfold tailWord_8203328
  simp only [CollatzResearch.WordTrace]
  refine ⟨149599976212375573863429319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199466634949834098484572425 149599976212375573863429319)
  ·
    refine ⟨224399964318563360795143979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149599976212375573863429319 224399964318563360795143979)
    ·
      refine ⟨336599946477845041192715969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224399964318563360795143979 336599946477845041192715969)
      ·
        refine ⟨252449959858383780894536977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336599946477845041192715969 252449959858383780894536977)
        ·
          refine ⟨189337469893787835670902733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252449959858383780894536977 189337469893787835670902733)
          ·
            refine ⟨71001551210170438376588525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189337469893787835670902733 71001551210170438376588525)
            ·
              refine ⟨26625581703813914391220697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71001551210170438376588525 26625581703813914391220697)
              ·
                refine ⟨19969186277860435793415523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26625581703813914391220697 19969186277860435793415523)
                ·
                  refine ⟨29953779416790653690123285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19969186277860435793415523 29953779416790653690123285)
                  ·
                    refine ⟨1404083410162061891724529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29953779416790653690123285 1404083410162061891724529)
                    ·
                      rfl

theorem cell23_8203328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_8203328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203328 prefixEnd_8203328 := by exact prefixLift 8203328
  have htrace : WordTrace (prefixWord ++ tailWord_8203328) baseStart_8203328 baseEnd_8203328 := by
    simpa [prefixWord, tailWord_8203328, baseEnd_8203328] using wordTrace_append hprefix tailTrace_8203328
  have hstable : (prefixWord ++ tailWord_8203328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203328).length < 2 ^ (prefixWord ++ tailWord_8203328).sum := by decide
  have hdescent : baseEnd_8203328 < baseStart_8203328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203345 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 2, 4]
def baseStart_8203345 : Nat := 118140960795 + 8203345 * 2 ^ 59
def prefixEnd_8203345 : Nat := 4983230072969 + 3 ^ 40 * 8203345 * 2
def baseEnd_8203345 : Nat := 1404086319885770702887003

theorem tailTrace_8203345 : CollatzResearch.WordTrace tailWord_8203345 prefixEnd_8203345 1404086319885770702887003 := by
  unfold tailWord_8203345
  simp only [CollatzResearch.WordTrace]
  refine ⟨299200572465689559630227489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199467048310459706420151659 299200572465689559630227489)
  ·
    refine ⟨224400429349267169722670617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299200572465689559630227489 224400429349267169722670617)
    ·
      refine ⟨168300322011950377292002963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224400429349267169722670617 168300322011950377292002963)
      ·
        refine ⟨252450483017925565938004445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168300322011950377292002963 252450483017925565938004445)
        ·
          refine ⟨94668931131722087226751667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252450483017925565938004445 94668931131722087226751667)
          ·
            refine ⟨142003396697583130840127501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94668931131722087226751667 142003396697583130840127501)
            ·
              refine ⟨53251273761593674065047813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142003396697583130840127501 53251273761593674065047813)
              ·
                refine ⟨9984613830298813887196465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53251273761593674065047813 9984613830298813887196465)
                ·
                  refine ⟨7488460372724110415397349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9984613830298813887196465 7488460372724110415397349)
                  ·
                    refine ⟨1404086319885770702887003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488460372724110415397349 1404086319885770702887003)
                    ·
                      rfl

theorem cell23_8203345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_8203345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203345 prefixEnd_8203345 := by exact prefixLift 8203345
  have htrace : WordTrace (prefixWord ++ tailWord_8203345) baseStart_8203345 baseEnd_8203345 := by
    simpa [prefixWord, tailWord_8203345, baseEnd_8203345] using wordTrace_append hprefix tailTrace_8203345
  have hstable : (prefixWord ++ tailWord_8203345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203345).length < 2 ^ (prefixWord ++ tailWord_8203345).sum := by decide
  have hdescent : baseEnd_8203345 < baseStart_8203345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203346 : List Nat := [3, 2, 2, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_8203346 : Nat := 118140960795 + 8203346 * 2 ^ 59
def prefixEnd_8203346 : Nat := 4983230072969 + 3 ^ 40 * 8203346 * 2
def baseEnd_8203346 : Nat := 4212259473137966604748505

theorem tailTrace_8203346 : CollatzResearch.WordTrace tailWord_8203346 prefixEnd_8203346 4212259473137966604748505 := by
  unfold tailWord_8203346
  simp only [CollatzResearch.WordTrace]
  refine ⟨74800152234671484200253473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199467072625790624534009261 74800152234671484200253473)
  ·
    refine ⟨56100114176003613150190105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74800152234671484200253473 56100114176003613150190105)
    ·
      refine ⟨42075085632002709862642579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56100114176003613150190105 42075085632002709862642579)
      ·
        refine ⟨63112628448004064793963869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42075085632002709862642579 63112628448004064793963869)
        ·
          refine ⟨23667235668001524297736451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63112628448004064793963869 23667235668001524297736451)
          ·
            refine ⟨35500853502002286446604677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23667235668001524297736451 35500853502002286446604677)
            ·
              refine ⟨6656410031625428708738377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35500853502002286446604677 6656410031625428708738377)
              ·
                refine ⟨4992307523719071531553783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6656410031625428708738377 4992307523719071531553783)
                ·
                  refine ⟨7488461285578607297330675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992307523719071531553783 7488461285578607297330675)
                  ·
                    refine ⟨11232691928367910945996013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7488461285578607297330675 11232691928367910945996013)
                    ·
                      refine ⟨4212259473137966604748505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11232691928367910945996013 4212259473137966604748505)
                      ·
                        rfl

theorem cell23_8203346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_8203346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203346 prefixEnd_8203346 := by exact prefixLift 8203346
  have htrace : WordTrace (prefixWord ++ tailWord_8203346) baseStart_8203346 baseEnd_8203346 := by
    simpa [prefixWord, tailWord_8203346, baseEnd_8203346] using wordTrace_append hprefix tailTrace_8203346
  have hstable : (prefixWord ++ tailWord_8203346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203346).length < 2 ^ (prefixWord ++ tailWord_8203346).sum := by decide
  have hdescent : baseEnd_8203346 < baseStart_8203346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203348 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_8203348 : Nat := 118140960795 + 8203348 * 2 ^ 59
def prefixEnd_8203348 : Nat := 4983230072969 + 3 ^ 40 * 8203348 * 2
def baseEnd_8203348 : Nat := 4212260500099275596923495

theorem tailTrace_8203348 : CollatzResearch.WordTrace tailWord_8203348 prefixEnd_8203348 4212260500099275596923495 := by
  unfold tailWord_8203348
  simp only [CollatzResearch.WordTrace]
  refine ⟨149600340942339345571293349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199467121256452460761724465 149600340942339345571293349)
  ·
    refine ⟨28050063926688627294617503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149600340942339345571293349 28050063926688627294617503)
    ·
      refine ⟨42075095890032940941926255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28050063926688627294617503 42075095890032940941926255)
      ·
        refine ⟨63112643835049411412889383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42075095890032940941926255 63112643835049411412889383)
        ·
          refine ⟨94668965752574117119334075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63112643835049411412889383 94668965752574117119334075)
          ·
            refine ⟨142003448628861175679001113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94668965752574117119334075 142003448628861175679001113)
            ·
              refine ⟨106502586471645881759250835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142003448628861175679001113 106502586471645881759250835)
              ·
                refine ⟨159753879707468822638876253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106502586471645881759250835 159753879707468822638876253)
                ·
                  refine ⟨59907704890300808489578595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159753879707468822638876253 59907704890300808489578595)
                  ·
                    refine ⟨89861557335451212734367893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59907704890300808489578595 89861557335451212734367893)
                    ·
                      refine ⟨4212260500099275596923495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89861557335451212734367893 4212260500099275596923495)
                      ·
                        rfl

theorem cell23_8203348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_8203348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203348 prefixEnd_8203348 := by exact prefixLift 8203348
  have htrace : WordTrace (prefixWord ++ tailWord_8203348) baseStart_8203348 baseEnd_8203348 := by
    simpa [prefixWord, tailWord_8203348, baseEnd_8203348] using wordTrace_append hprefix tailTrace_8203348
  have hstable : (prefixWord ++ tailWord_8203348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203348).length < 2 ^ (prefixWord ++ tailWord_8203348).sum := by decide
  have hdescent : baseEnd_8203348 < baseStart_8203348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203352 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 3, 2, 2]
def baseStart_8203352 : Nat := 118140960795 + 8203352 * 2 ^ 59
def prefixEnd_8203352 : Nat := 4983230072969 + 3 ^ 40 * 8203352 * 2
def baseEnd_8203352 : Nat := 4212262554021893581273477

theorem tailTrace_8203352 : CollatzResearch.WordTrace tailWord_8203352 prefixEnd_8203352 4212262554021893581273477 := by
  unfold tailWord_8203352
  simp only [CollatzResearch.WordTrace]
  refine ⟨149600413888332099912866155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199467218517776133217154873 149600413888332099912866155)
  ·
    refine ⟨224400620832498149869299233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149600413888332099912866155 224400620832498149869299233)
    ·
      refine ⟨168300465624373612401974425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224400620832498149869299233 168300465624373612401974425)
      ·
        refine ⟨126225349218280209301480819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168300465624373612401974425 126225349218280209301480819)
        ·
          refine ⟨189338023827420313952221229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126225349218280209301480819 189338023827420313952221229)
          ·
            refine ⟨71001758935282617732082961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189338023827420313952221229 71001758935282617732082961)
            ·
              refine ⟨53251319201461963299062221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71001758935282617732082961 53251319201461963299062221)
              ·
                refine ⟨19969244700548236237148333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53251319201461963299062221 19969244700548236237148333)
                ·
                  refine ⟨7488466762705588588930625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19969244700548236237148333 7488466762705588588930625)
                  ·
                    refine ⟨5616350072029191441697969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7488466762705588588930625 5616350072029191441697969)
                    ·
                      refine ⟨4212262554021893581273477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5616350072029191441697969 4212262554021893581273477)
                      ·
                        rfl

theorem cell23_8203352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_8203352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203352 prefixEnd_8203352 := by exact prefixLift 8203352
  have htrace : WordTrace (prefixWord ++ tailWord_8203352) baseStart_8203352 baseEnd_8203352 := by
    simpa [prefixWord, tailWord_8203352, baseEnd_8203352] using wordTrace_append hprefix tailTrace_8203352
  have hstable : (prefixWord ++ tailWord_8203352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203352).length < 2 ^ (prefixWord ++ tailWord_8203352).sum := by decide
  have hdescent : baseEnd_8203352 < baseStart_8203352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203362 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_8203362 : Nat := 118140960795 + 8203362 * 2 ^ 59
def prefixEnd_8203362 : Nat := 4983230072969 + 3 ^ 40 * 8203362 * 2
def baseEnd_8203362 : Nat := 1404089229609479514049477

theorem tailTrace_8203362 : CollatzResearch.WordTrace tailWord_8203362 prefixEnd_8203362 1404089229609479514049477 := by
  unfold tailWord_8203362
  simp only [CollatzResearch.WordTrace]
  refine ⟨74800298126656992883399085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199467461671085314355730893 74800298126656992883399085)
  ·
    refine ⟨28050111797496372331274657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74800298126656992883399085 28050111797496372331274657)
    ·
      refine ⟨21037583848122279248455993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28050111797496372331274657 21037583848122279248455993)
      ·
        refine ⟨15778187886091709436341995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21037583848122279248455993 15778187886091709436341995)
        ·
          refine ⟨23667281829137564154512993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15778187886091709436341995 23667281829137564154512993)
          ·
            refine ⟨17750461371853173115884745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23667281829137564154512993 17750461371853173115884745)
            ·
              refine ⟨13312846028889879836913559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17750461371853173115884745 13312846028889879836913559)
              ·
                refine ⟨19969269043334819755370339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13312846028889879836913559 19969269043334819755370339)
                ·
                  refine ⟨29953903565002229633055509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19969269043334819755370339 29953903565002229633055509)
                  ·
                    refine ⟨1404089229609479514049477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29953903565002229633055509 1404089229609479514049477)
                    ·
                      rfl

theorem cell23_8203362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_8203362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203362 prefixEnd_8203362 := by exact prefixLift 8203362
  have htrace : WordTrace (prefixWord ++ tailWord_8203362) baseStart_8203362 baseEnd_8203362 := by
    simpa [prefixWord, tailWord_8203362, baseEnd_8203362] using wordTrace_append hprefix tailTrace_8203362
  have hstable : (prefixWord ++ tailWord_8203362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203362).length < 2 ^ (prefixWord ++ tailWord_8203362).sum := by decide
  have hdescent : baseEnd_8203362 < baseStart_8203362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203365 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_8203365 : Nat := 118140960795 + 8203365 * 2 ^ 59
def prefixEnd_8203365 : Nat := 4983230072969 + 3 ^ 40 * 8203365 * 2
def baseEnd_8203365 : Nat := 4212269229270402030410917

theorem tailTrace_8203365 : CollatzResearch.WordTrace tailWord_8203365 prefixEnd_8203365 4212269229270402030410917 := by
  unfold tailWord_8203365
  simp only [CollatzResearch.WordTrace]
  refine ⟨299201301925617103045955549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199467534617078068697303699 299201301925617103045955549)
  ·
    refine ⟨112200488222106413642233331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299201301925617103045955549 112200488222106413642233331)
    ·
      refine ⟨168300732333159620463349997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112200488222106413642233331 168300732333159620463349997)
      ·
        refine ⟨63112774624934857673756249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168300732333159620463349997 63112774624934857673756249)
        ·
          refine ⟨47334580968701143255317187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63112774624934857673756249 47334580968701143255317187)
          ·
            refine ⟨71001871453051714882975781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47334580968701143255317187 71001871453051714882975781)
            ·
              refine ⟨13312850897447196540557959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71001871453051714882975781 13312850897447196540557959)
              ·
                refine ⟨19969276346170794810836939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13312850897447196540557959 19969276346170794810836939)
                ·
                  refine ⟨29953914519256192216255409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19969276346170794810836939 29953914519256192216255409)
                  ·
                    refine ⟨22465435889442144162191557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29953914519256192216255409 22465435889442144162191557)
                    ·
                      refine ⟨4212269229270402030410917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22465435889442144162191557 4212269229270402030410917)
                      ·
                        rfl

theorem cell23_8203365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_8203365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203365 prefixEnd_8203365 := by exact prefixLift 8203365
  have htrace : WordTrace (prefixWord ++ tailWord_8203365) baseStart_8203365 baseEnd_8203365 := by
    simpa [prefixWord, tailWord_8203365, baseEnd_8203365] using wordTrace_append hprefix tailTrace_8203365
  have hstable : (prefixWord ++ tailWord_8203365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203365).length < 2 ^ (prefixWord ++ tailWord_8203365).sum := by decide
  have hdescent : baseEnd_8203365 < baseStart_8203365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203402 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_8203402 : Nat := 118140960795 + 8203402 * 2 ^ 59
def prefixEnd_8203402 : Nat := 4983230072969 + 3 ^ 40 * 8203402 * 2
def baseEnd_8203402 : Nat := 4212288228054618385648247

theorem tailTrace_8203402 : CollatzResearch.WordTrace tailWord_8203402 prefixEnd_8203402 4212288228054618385648247 := by
  unfold tailWord_8203402
  simp only [CollatzResearch.WordTrace]
  refine ⟨74800662856620764591263115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199468434284322038910034973 74800662856620764591263115)
  ·
    refine ⟨112200994284931146886894673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74800662856620764591263115 112200994284931146886894673)
    ·
      refine ⟨84150745713698360165171005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112200994284931146886894673 84150745713698360165171005)
      ·
        refine ⟨31556529642636885061939127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84150745713698360165171005 31556529642636885061939127)
        ·
          refine ⟨47334794463955327592908691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31556529642636885061939127 47334794463955327592908691)
          ·
            refine ⟨71002191695932991389363037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47334794463955327592908691 71002191695932991389363037)
            ·
              refine ⟨26625821885974871771011139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71002191695932991389363037 26625821885974871771011139)
              ·
                refine ⟨39938732828962307656516709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26625821885974871771011139 39938732828962307656516709)
                ·
                  refine ⟨7488512405430432685596883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39938732828962307656516709 7488512405430432685596883)
                  ·
                    refine ⟨11232768608145649028395325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7488512405430432685596883 11232768608145649028395325)
                    ·
                      refine ⟨4212288228054618385648247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11232768608145649028395325 4212288228054618385648247)
                      ·
                        rfl

theorem cell23_8203402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_8203402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203402 prefixEnd_8203402 := by exact prefixLift 8203402
  have htrace : WordTrace (prefixWord ++ tailWord_8203402) baseStart_8203402 baseEnd_8203402 := by
    simpa [prefixWord, tailWord_8203402, baseEnd_8203402] using wordTrace_append hprefix tailTrace_8203402
  have hstable : (prefixWord ++ tailWord_8203402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203402).length < 2 ^ (prefixWord ++ tailWord_8203402).sum := by decide
  have hdescent : baseEnd_8203402 < baseStart_8203402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203408 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_8203408 : Nat := 118140960795 + 8203408 * 2 ^ 59
def prefixEnd_8203408 : Nat := 4983230072969 + 3 ^ 40 * 8203408 * 2
def baseEnd_8203408 : Nat := 4212291308938545362173219

theorem tailTrace_8203408 : CollatzResearch.WordTrace tailWord_8203408 prefixEnd_8203408 4212291308938545362173219 := by
  unfold tailWord_8203408
  simp only [CollatzResearch.WordTrace]
  refine ⟨149601435132230660694885439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199468580176307547593180585 149601435132230660694885439)
  ·
    refine ⟨224402152698345991042328159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149601435132230660694885439 224402152698345991042328159)
    ·
      refine ⟨336603229047518986563492239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224402152698345991042328159 336603229047518986563492239)
      ·
        refine ⟨504904843571278479845238359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336603229047518986563492239 504904843571278479845238359)
        ·
          refine ⟨757357265356917719767857539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504904843571278479845238359 757357265356917719767857539)
          ·
            refine ⟨1136035898035376579651786309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757357265356917719767857539 1136035898035376579651786309)
            ·
              refine ⟨213006730881633108684709933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1136035898035376579651786309 213006730881633108684709933)
              ·
                refine ⟨79877524080612415756766225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213006730881633108684709933 79877524080612415756766225)
                ·
                  refine ⟨59908143060459311817574669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79877524080612415756766225 59908143060459311817574669)
                  ·
                    refine ⟨22465553647672241931590501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59908143060459311817574669 22465553647672241931590501)
                    ·
                      refine ⟨4212291308938545362173219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22465553647672241931590501 4212291308938545362173219)
                      ·
                        rfl

theorem cell23_8203408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_8203408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203408 prefixEnd_8203408 := by exact prefixLift 8203408
  have htrace : WordTrace (prefixWord ++ tailWord_8203408) baseStart_8203408 baseEnd_8203408 := by
    simpa [prefixWord, tailWord_8203408, baseEnd_8203408] using wordTrace_append hprefix tailTrace_8203408
  have hstable : (prefixWord ++ tailWord_8203408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203408).length < 2 ^ (prefixWord ++ tailWord_8203408).sum := by decide
  have hdescent : baseEnd_8203408 < baseStart_8203408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203429 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 1, 3, 2]
def baseStart_8203429 : Nat := 118140960795 + 8203429 * 2 ^ 59
def prefixEnd_8203429 : Nat := 4983230072969 + 3 ^ 40 * 8203429 * 2
def baseEnd_8203429 : Nat := 4212302092032289780010623

theorem tailTrace_8203429 : CollatzResearch.WordTrace tailWord_8203429 prefixEnd_8203429 4212302092032289780010623 := by
  unfold tailWord_8203429
  simp only [CollatzResearch.WordTrace]
  refine ⟨299203636197385241976285341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199469090798256827984190227 299203636197385241976285341)
  ·
    refine ⟨112201363574019465741107003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299203636197385241976285341 112201363574019465741107003)
    ·
      refine ⟨168302045361029198611660505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112201363574019465741107003 168302045361029198611660505)
      ·
        refine ⟨126226534020771898958745379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168302045361029198611660505 126226534020771898958745379)
        ·
          refine ⟨189339801031157848438118069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126226534020771898958745379 189339801031157848438118069)
          ·
            refine ⟨17750606346671048291073569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189339801031157848438118069 17750606346671048291073569)
            ·
              refine ⟨13312954760003286218305177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17750606346671048291073569 13312954760003286218305177)
              ·
                refine ⟨9984716070002464663728883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13312954760003286218305177 9984716070002464663728883)
                ·
                  refine ⟨14977074105003696995593325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9984716070002464663728883 14977074105003696995593325)
                  ·
                    refine ⟨5616402789376386373347497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14977074105003696995593325 5616402789376386373347497)
                    ·
                      refine ⟨4212302092032289780010623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5616402789376386373347497 4212302092032289780010623)
                      ·
                        rfl

theorem cell23_8203429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_8203429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203429 prefixEnd_8203429 := by exact prefixLift 8203429
  have htrace : WordTrace (prefixWord ++ tailWord_8203429) baseStart_8203429 baseEnd_8203429 := by
    simpa [prefixWord, tailWord_8203429, baseEnd_8203429] using wordTrace_append hprefix tailTrace_8203429
  have hstable : (prefixWord ++ tailWord_8203429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203429).length < 2 ^ (prefixWord ++ tailWord_8203429).sum := by decide
  have hdescent : baseEnd_8203429 < baseStart_8203429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203516 : List Nat := [2, 2, 2, 1, 5, 2, 2, 2, 5]
def baseStart_8203516 : Nat := 118140960795 + 8203516 * 2 ^ 59
def prefixEnd_8203516 : Nat := 4983230072969 + 3 ^ 40 * 8203516 * 2
def baseEnd_8203516 : Nat := 468038529427692326624747

theorem tailTrace_8203516 : CollatzResearch.WordTrace tailWord_8203516 prefixEnd_8203516 468038529427692326624747 := by
  unfold tailWord_8203516
  simp only [CollatzResearch.WordTrace]
  refine ⟨149603404674035027917351201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199471206232046703889801601 149603404674035027917351201)
  ·
    refine ⟨112202553505526270938013401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149603404674035027917351201 112202553505526270938013401)
    ·
      refine ⟨84151915129144703203510051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112202553505526270938013401 84151915129144703203510051)
      ·
        refine ⟨126227872693717054805265077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84151915129144703203510051 126227872693717054805265077)
        ·
          refine ⟨11833863065035973887993601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126227872693717054805265077 11833863065035973887993601)
          ·
            refine ⟨8875397298776980415995201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11833863065035973887993601 8875397298776980415995201)
            ·
              refine ⟨6656547974082735311996401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8875397298776980415995201 6656547974082735311996401)
              ·
                refine ⟨4992410980562051483997301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6656547974082735311996401 4992410980562051483997301)
                ·
                  refine ⟨468038529427692326624747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4992410980562051483997301 468038529427692326624747)
                  ·
                    rfl

theorem cell23_8203516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_8203516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203516 prefixEnd_8203516 := by exact prefixLift 8203516
  have htrace : WordTrace (prefixWord ++ tailWord_8203516) baseStart_8203516 baseEnd_8203516 := by
    simpa [prefixWord, tailWord_8203516, baseEnd_8203516] using wordTrace_append hprefix tailTrace_8203516
  have hstable : (prefixWord ++ tailWord_8203516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203516).length < 2 ^ (prefixWord ++ tailWord_8203516).sum := by decide
  have hdescent : baseEnd_8203516 < baseStart_8203516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203532 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 1, 6, 2]
def baseStart_8203532 : Nat := 118140960795 + 8203532 * 2 ^ 59
def prefixEnd_8203532 : Nat := 4983230072969 + 3 ^ 40 * 8203532 * 2
def baseEnd_8203532 : Nat := 4212354980539702877022649

theorem tailTrace_8203532 : CollatzResearch.WordTrace tailWord_8203532 prefixEnd_8203532 4212354980539702877022649 := by
  unfold tailWord_8203532
  simp only [CollatzResearch.WordTrace]
  refine ⟨149603696458006045283642425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199471595277341393711523233 149603696458006045283642425)
  ·
    refine ⟨112202772343504533962731819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149603696458006045283642425 112202772343504533962731819)
    ·
      refine ⟨168304158515256800944097729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112202772343504533962731819 168304158515256800944097729)
      ·
        refine ⟨126228118886442600708073297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168304158515256800944097729 126228118886442600708073297)
        ·
          refine ⟨94671089164831950531054973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126228118886442600708073297 94671089164831950531054973)
          ·
            refine ⟨35501658436811981449145615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94671089164831950531054973 35501658436811981449145615)
            ·
              refine ⟨53252487655217972173718423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35501658436811981449145615 53252487655217972173718423)
              ·
                refine ⟨79878731482826958260577635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53252487655217972173718423 79878731482826958260577635)
                ·
                  refine ⟨119818097224240437390866453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79878731482826958260577635 119818097224240437390866453)
                  ·
                    refine ⟨5616473307386270502696865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119818097224240437390866453 5616473307386270502696865)
                    ·
                      refine ⟨4212354980539702877022649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5616473307386270502696865 4212354980539702877022649)
                      ·
                        rfl

theorem cell23_8203532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_8203532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203532 prefixEnd_8203532 := by exact prefixLift 8203532
  have htrace : WordTrace (prefixWord ++ tailWord_8203532) baseStart_8203532 baseEnd_8203532 := by
    simpa [prefixWord, tailWord_8203532, baseEnd_8203532] using wordTrace_append hprefix tailTrace_8203532
  have hstable : (prefixWord ++ tailWord_8203532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203532).length < 2 ^ (prefixWord ++ tailWord_8203532).sum := by decide
  have hdescent : baseEnd_8203532 < baseStart_8203532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203549 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_8203549 : Nat := 118140960795 + 8203549 * 2 ^ 59
def prefixEnd_8203549 : Nat := 4983230072969 + 3 ^ 40 * 8203549 * 2
def baseEnd_8203549 : Nat := 4212363709710829310510071

theorem tailTrace_8203549 : CollatzResearch.WordTrace tailWord_8203549 prefixEnd_8203549 4212363709710829310510071 := by
  unfold tailWord_8203549
  simp only [CollatzResearch.WordTrace]
  refine ⟨299208012956950502470653701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199472008637967001647102467 299208012956950502470653701)
  ·
    refine ⟨56101502429428219213247569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299208012956950502470653701 56101502429428219213247569)
    ·
      refine ⟨42076126822071164409935677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56101502429428219213247569 42076126822071164409935677)
      ·
        refine ⟨15778547558276686653725879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42076126822071164409935677 15778547558276686653725879)
        ·
          refine ⟨23667821337415029980588819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15778547558276686653725879 23667821337415029980588819)
          ·
            refine ⟨35501732006122544970883229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23667821337415029980588819 35501732006122544970883229)
            ·
              refine ⟨13313149502295954364081211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35501732006122544970883229 13313149502295954364081211)
              ·
                refine ⟨19969724253443931546121817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13313149502295954364081211 19969724253443931546121817)
                ·
                  refine ⟨14977293190082948659591363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19969724253443931546121817 14977293190082948659591363)
                  ·
                    refine ⟨22465939785124422989387045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14977293190082948659591363 22465939785124422989387045)
                    ·
                      refine ⟨4212363709710829310510071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22465939785124422989387045 4212363709710829310510071)
                      ·
                        rfl

theorem cell23_8203549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_8203549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203549 prefixEnd_8203549 := by exact prefixLift 8203549
  have htrace : WordTrace (prefixWord ++ tailWord_8203549) baseStart_8203549 baseEnd_8203549 := by
    simpa [prefixWord, tailWord_8203549, baseEnd_8203549] using wordTrace_append hprefix tailTrace_8203549
  have hstable : (prefixWord ++ tailWord_8203549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203549).length < 2 ^ (prefixWord ++ tailWord_8203549).sum := by decide
  have hdescent : baseEnd_8203549 < baseStart_8203549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203562 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_8203562 : Nat := 118140960795 + 8203562 * 2 ^ 59
def prefixEnd_8203562 : Nat := 4983230072969 + 3 ^ 40 * 8203562 * 2
def baseEnd_8203562 : Nat := 4212370384959337759647511

theorem tailTrace_8203562 : CollatzResearch.WordTrace tailWord_8203562 prefixEnd_8203562 4212370384959337759647511 := by
  unfold tailWord_8203562
  simp only [CollatzResearch.WordTrace]
  refine ⟨74802121776475851422719235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199472324737268937127251293 74802121776475851422719235)
  ·
    refine ⟨112203182664713777134078853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74802121776475851422719235 112203182664713777134078853)
    ·
      refine ⟨21038096749633833212639785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112203182664713777134078853 21038096749633833212639785)
      ·
        refine ⟨15778572562225374909479839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21038096749633833212639785 15778572562225374909479839)
        ·
          refine ⟨23667858843338062364219759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15778572562225374909479839 23667858843338062364219759)
          ·
            refine ⟨35501788265007093546329639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23667858843338062364219759 35501788265007093546329639)
            ·
              refine ⟨53252682397510640319494459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35501788265007093546329639 53252682397510640319494459)
              ·
                refine ⟨79879023596265960479241689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53252682397510640319494459 79879023596265960479241689)
                ·
                  refine ⟨59909267697199470359431267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79879023596265960479241689 59909267697199470359431267)
                  ·
                    refine ⟨89863901545799205539146901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59909267697199470359431267 89863901545799205539146901)
                    ·
                      refine ⟨4212370384959337759647511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89863901545799205539146901 4212370384959337759647511)
                      ·
                        rfl

theorem cell23_8203562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_8203562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203562 prefixEnd_8203562 := by exact prefixLift 8203562
  have htrace : WordTrace (prefixWord ++ tailWord_8203562) baseStart_8203562 baseEnd_8203562 := by
    simpa [prefixWord, tailWord_8203562, baseEnd_8203562] using wordTrace_append hprefix tailTrace_8203562
  have hstable : (prefixWord ++ tailWord_8203562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203562).length < 2 ^ (prefixWord ++ tailWord_8203562).sum := by decide
  have hdescent : baseEnd_8203562 < baseStart_8203562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203572 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 8]
def baseStart_8203572 : Nat := 118140960795 + 8203572 * 2 ^ 59
def prefixEnd_8203572 : Nat := 4983230072969 + 3 ^ 40 * 8203572 * 2
def baseEnd_8203572 : Nat := 468041724418431413391385

theorem tailTrace_8203572 : CollatzResearch.WordTrace tailWord_8203572 prefixEnd_8203572 468041724418431413391385 := by
  unfold tailWord_8203572
  simp only [CollatzResearch.WordTrace]
  refine ⟨149604425917933588699370485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199472567890578118265827313 149604425917933588699370485)
  ·
    refine ⟨14025414929806273940565983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149604425917933588699370485 14025414929806273940565983)
    ·
      refine ⟨21038122394709410910848975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14025414929806273940565983 21038122394709410910848975)
      ·
        refine ⟨31557183592064116366273463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21038122394709410910848975 31557183592064116366273463)
        ·
          refine ⟨47335775388096174549410195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31557183592064116366273463 47335775388096174549410195)
          ·
            refine ⟨71003663082144261824115293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47335775388096174549410195 71003663082144261824115293)
            ·
              refine ⟨26626373655804098184043235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71003663082144261824115293 26626373655804098184043235)
              ·
                refine ⟨39939560483706147276064853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26626373655804098184043235 39939560483706147276064853)
                ·
                  refine ⟨468041724418431413391385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39939560483706147276064853 468041724418431413391385)
                  ·
                    rfl

theorem cell23_8203572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_8203572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203572 prefixEnd_8203572 := by exact prefixLift 8203572
  have htrace : WordTrace (prefixWord ++ tailWord_8203572) baseStart_8203572 baseEnd_8203572 := by
    simpa [prefixWord, tailWord_8203572, baseEnd_8203572] using wordTrace_append hprefix tailTrace_8203572
  have hstable : (prefixWord ++ tailWord_8203572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203572).length < 2 ^ (prefixWord ++ tailWord_8203572).sum := by decide
  have hdescent : baseEnd_8203572 < baseStart_8203572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203615 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 3, 6]
def baseStart_8203615 : Nat := 118140960795 + 8203615 * 2 ^ 59
def prefixEnd_8203615 : Nat := 4983230072969 + 3 ^ 40 * 8203615 * 2
def baseEnd_8203615 : Nat := 1404132533144675350761589

theorem tailTrace_8203615 : CollatzResearch.WordTrace tailWord_8203615 prefixEnd_8203615 1404132533144675350761589 := by
  unfold tailWord_8203615
  simp only [CollatzResearch.WordTrace]
  refine ⟨299210420174711395742556299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199473613449807597161704199 299210420174711395742556299)
  ·
    refine ⟨448815630262067093613834449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299210420174711395742556299 448815630262067093613834449)
    ·
      refine ⟨336611722696550320210375837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448815630262067093613834449 336611722696550320210375837)
      ·
        refine ⟨126229396011206370078890939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336611722696550320210375837 126229396011206370078890939)
        ·
          refine ⟨189344094016809555118336409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126229396011206370078890939 189344094016809555118336409)
          ·
            refine ⟨142008070512607166338752307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189344094016809555118336409 142008070512607166338752307)
            ·
              refine ⟨213012105768910749508128461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142008070512607166338752307 213012105768910749508128461)
              ·
                refine ⟨79879539663341531065548173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213012105768910749508128461 79879539663341531065548173)
                ·
                  refine ⟨29954827373753074149580565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79879539663341531065548173 29954827373753074149580565)
                  ·
                    refine ⟨1404132533144675350761589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29954827373753074149580565 1404132533144675350761589)
                    ·
                      rfl

theorem cell23_8203615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_8203615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203615 prefixEnd_8203615 := by exact prefixLift 8203615
  have htrace : WordTrace (prefixWord ++ tailWord_8203615) baseStart_8203615 baseEnd_8203615 := by
    simpa [prefixWord, tailWord_8203615, baseEnd_8203615] using wordTrace_append hprefix tailTrace_8203615
  have hstable : (prefixWord ++ tailWord_8203615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203615).length < 2 ^ (prefixWord ++ tailWord_8203615).sum := by decide
  have hdescent : baseEnd_8203615 < baseStart_8203615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203632 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 4, 4]
def baseStart_8203632 : Nat := 118140960795 + 8203632 * 2 ^ 59
def prefixEnd_8203632 : Nat := 4983230072969 + 3 ^ 40 * 8203632 * 2
def baseEnd_8203632 : Nat := 1404135442868384161924063

theorem tailTrace_8203632 : CollatzResearch.WordTrace tailWord_8203632 prefixEnd_8203632 1404135442868384161924063 := by
  unfold tailWord_8203632
  simp only [CollatzResearch.WordTrace]
  refine ⟨149605520107824903822962575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199474026810433205097283433 149605520107824903822962575)
  ·
    refine ⟨224408280161737355734443863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149605520107824903822962575 224408280161737355734443863)
    ·
      refine ⟨336612420242606033601665795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224408280161737355734443863 336612420242606033601665795)
      ·
        refine ⟨504918630363909050402498693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336612420242606033601665795 504918630363909050402498693)
        ·
          refine ⟨94672243193232946950468505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504918630363909050402498693 94672243193232946950468505)
          ·
            refine ⟨71004182394924710212851379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94672243193232946950468505 71004182394924710212851379)
            ·
              refine ⟨106506273592387065319277069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71004182394924710212851379 106506273592387065319277069)
              ·
                refine ⟨39939852597145149494728901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106506273592387065319277069 39939852597145149494728901)
                ·
                  refine ⟨7488722361964715530261669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39939852597145149494728901 7488722361964715530261669)
                  ·
                    refine ⟨1404135442868384161924063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488722361964715530261669 1404135442868384161924063)
                    ·
                      rfl

theorem cell23_8203632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 4].length) (baseStart_8203632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203632 prefixEnd_8203632 := by exact prefixLift 8203632
  have htrace : WordTrace (prefixWord ++ tailWord_8203632) baseStart_8203632 baseEnd_8203632 := by
    simpa [prefixWord, tailWord_8203632, baseEnd_8203632] using wordTrace_append hprefix tailTrace_8203632
  have hstable : (prefixWord ++ tailWord_8203632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203632).length < 2 ^ (prefixWord ++ tailWord_8203632).sum := by decide
  have hdescent : baseEnd_8203632 < baseStart_8203632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203635 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 4]
def baseStart_8203635 : Nat := 118140960795 + 8203635 * 2 ^ 59
def prefixEnd_8203635 : Nat := 4983230072969 + 3 ^ 40 * 8203635 * 2
def baseEnd_8203635 : Nat := 4212407869047115974034675

theorem tailTrace_8203635 : CollatzResearch.WordTrace tailWord_8203635 prefixEnd_8203635 4212407869047115974034675 := by
  unfold tailWord_8203635
  simp only [CollatzResearch.WordTrace]
  refine ⟨299211149634638939158284359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199474099756425959438856239 299211149634638939158284359)
  ·
    refine ⟨448816724451958408737426539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299211149634638939158284359 448816724451958408737426539)
    ·
      refine ⟨673225086677937613106139809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448816724451958408737426539 673225086677937613106139809)
      ·
        refine ⟨504918815008453209829604857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673225086677937613106139809 504918815008453209829604857)
        ·
          refine ⟨378689111256339907372203643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504918815008453209829604857 378689111256339907372203643)
          ·
            refine ⟨568033666884509861058305465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378689111256339907372203643 568033666884509861058305465)
            ·
              refine ⟨426025250163382395793729099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568033666884509861058305465 426025250163382395793729099)
              ·
                refine ⟨639037875245073593690593649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426025250163382395793729099 639037875245073593690593649)
                ·
                  refine ⟨479278406433805195267945237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639037875245073593690593649 479278406433805195267945237)
                  ·
                    refine ⟨22466175301584618528184933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 479278406433805195267945237 22466175301584618528184933)
                    ·
                      refine ⟨4212407869047115974034675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22466175301584618528184933 4212407869047115974034675)
                      ·
                        rfl

theorem cell23_8203635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_8203635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203635 prefixEnd_8203635 := by exact prefixLift 8203635
  have htrace : WordTrace (prefixWord ++ tailWord_8203635) baseStart_8203635 baseEnd_8203635 := by
    simpa [prefixWord, tailWord_8203635, baseEnd_8203635] using wordTrace_append hprefix tailTrace_8203635
  have hstable : (prefixWord ++ tailWord_8203635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203635).length < 2 ^ (prefixWord ++ tailWord_8203635).sum := by decide
  have hdescent : baseEnd_8203635 < baseStart_8203635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203642 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_8203642 : Nat := 118140960795 + 8203642 * 2 ^ 59
def prefixEnd_8203642 : Nat := 4983230072969 + 3 ^ 40 * 8203642 * 2
def baseEnd_8203642 : Nat := 4212411463411697446647143

theorem tailTrace_8203642 : CollatzResearch.WordTrace tailWord_8203642 prefixEnd_8203642 4212411463411697446647143 := by
  unfold tailWord_8203642
  simp only [CollatzResearch.WordTrace]
  refine ⟨74802851236403394838447295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199474269963742386235859453 74802851236403394838447295)
  ·
    refine ⟨112204276854605092257670943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74802851236403394838447295 112204276854605092257670943)
    ·
      refine ⟨168306415281907638386506415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112204276854605092257670943 168306415281907638386506415)
      ·
        refine ⟨252459622922861457579759623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168306415281907638386506415 252459622922861457579759623)
        ·
          refine ⟨378689434384292186369639435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252459622922861457579759623 378689434384292186369639435)
          ·
            refine ⟨568034151576438279554459153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378689434384292186369639435 568034151576438279554459153)
            ·
              refine ⟨426025613682328709665844365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568034151576438279554459153 426025613682328709665844365)
              ·
                refine ⟨159759605130873266124691637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426025613682328709665844365 159759605130873266124691637)
                ·
                  refine ⟨14977462981019368699189841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159759605130873266124691637 14977462981019368699189841)
                  ·
                    refine ⟨11233097235764526524392381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14977462981019368699189841 11233097235764526524392381)
                    ·
                      refine ⟨4212411463411697446647143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11233097235764526524392381 4212411463411697446647143)
                      ·
                        rfl

theorem cell23_8203642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_8203642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203642 prefixEnd_8203642 := by exact prefixLift 8203642
  have htrace : WordTrace (prefixWord ++ tailWord_8203642) baseStart_8203642 baseEnd_8203642 := by
    simpa [prefixWord, tailWord_8203642, baseEnd_8203642] using wordTrace_append hprefix tailTrace_8203642
  have hstable : (prefixWord ++ tailWord_8203642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203642).length < 2 ^ (prefixWord ++ tailWord_8203642).sum := by decide
  have hdescent : baseEnd_8203642 < baseStart_8203642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203652 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_8203652 : Nat := 118140960795 + 8203652 * 2 ^ 59
def prefixEnd_8203652 : Nat := 4983230072969 + 3 ^ 40 * 8203652 * 2
def baseEnd_8203652 : Nat := 4212416598218242407522097

theorem tailTrace_8203652 : CollatzResearch.WordTrace tailWord_8203652 prefixEnd_8203652 4212416598218242407522097 := by
  unfold tailWord_8203652
  simp only [CollatzResearch.WordTrace]
  refine ⟨149605884837788675530826605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199474513117051567374435473 149605884837788675530826605)
  ·
    refine ⟨56102206814170753324059977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149605884837788675530826605 56102206814170753324059977)
    ·
      refine ⟨42076655110628064993044983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56102206814170753324059977 42076655110628064993044983)
      ·
        refine ⟨63114982665942097489567475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42076655110628064993044983 63114982665942097489567475)
        ·
          refine ⟨94672473998913146234351213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63114982665942097489567475 94672473998913146234351213)
          ·
            refine ⟨35502177749592429837881705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94672473998913146234351213 35502177749592429837881705)
            ·
              refine ⟨26626633312194322378411279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35502177749592429837881705 26626633312194322378411279)
              ·
                refine ⟨39939949968291483567616919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26626633312194322378411279 39939949968291483567616919)
                ·
                  refine ⟨59909924952437225351425379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39939949968291483567616919 59909924952437225351425379)
                  ·
                    refine ⟨89864887428655838027138069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59909924952437225351425379 89864887428655838027138069)
                    ·
                      refine ⟨4212416598218242407522097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89864887428655838027138069 4212416598218242407522097)
                      ·
                        rfl

theorem cell23_8203652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_8203652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203652 prefixEnd_8203652 := by exact prefixLift 8203652
  have htrace : WordTrace (prefixWord ++ tailWord_8203652) baseStart_8203652 baseEnd_8203652 := by
    simpa [prefixWord, tailWord_8203652, baseEnd_8203652] using wordTrace_append hprefix tailTrace_8203652
  have hstable : (prefixWord ++ tailWord_8203652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203652).length < 2 ^ (prefixWord ++ tailWord_8203652).sum := by decide
  have hdescent : baseEnd_8203652 < baseStart_8203652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203656 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_8203656 : Nat := 118140960795 + 8203656 * 2 ^ 59
def prefixEnd_8203656 : Nat := 4983230072969 + 3 ^ 40 * 8203656 * 2
def baseEnd_8203656 : Nat := 4212418652140860391872079

theorem tailTrace_8203656 : CollatzResearch.WordTrace tailWord_8203656 prefixEnd_8203656 4212418652140860391872079 := by
  unfold tailWord_8203656
  simp only [CollatzResearch.WordTrace]
  refine ⟨149605957783781429872399411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199474610378375239829865881 149605957783781429872399411)
  ·
    refine ⟨224408936675672144808599117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149605957783781429872399411 224408936675672144808599117)
    ·
      refine ⟨84153351253377054303224669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224408936675672144808599117 84153351253377054303224669)
      ·
        refine ⟨31557506720016395363709251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84153351253377054303224669 31557506720016395363709251)
        ·
          refine ⟨47336260080024593045563877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31557506720016395363709251 47336260080024593045563877)
          ·
            refine ⟨8875548765004611196043227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47336260080024593045563877 8875548765004611196043227)
            ·
              refine ⟨13313323147506916794064841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8875548765004611196043227 13313323147506916794064841)
              ·
                refine ⟨9984992360630187595548631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13313323147506916794064841 9984992360630187595548631)
                ·
                  refine ⟨14977488540945281393322947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9984992360630187595548631 14977488540945281393322947)
                  ·
                    refine ⟨22466232811417922089984421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14977488540945281393322947 22466232811417922089984421)
                    ·
                      refine ⟨4212418652140860391872079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22466232811417922089984421 4212418652140860391872079)
                      ·
                        rfl

theorem cell23_8203656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_8203656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203656 prefixEnd_8203656 := by exact prefixLift 8203656
  have htrace : WordTrace (prefixWord ++ tailWord_8203656) baseStart_8203656 baseEnd_8203656 := by
    simpa [prefixWord, tailWord_8203656, baseEnd_8203656] using wordTrace_append hprefix tailTrace_8203656
  have hstable : (prefixWord ++ tailWord_8203656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203656).length < 2 ^ (prefixWord ++ tailWord_8203656).sum := by decide
  have hdescent : baseEnd_8203656 < baseStart_8203656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203665 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_8203665 : Nat := 118140960795 + 8203665 * 2 ^ 59
def prefixEnd_8203665 : Nat := 4983230072969 + 3 ^ 40 * 8203665 * 2
def baseEnd_8203665 : Nat := 4212423273466750856659537

theorem tailTrace_8203665 : CollatzResearch.WordTrace tailWord_8203665 prefixEnd_8203665 4212423273466750856659537 := by
  unfold tailWord_8203665
  simp only [CollatzResearch.WordTrace]
  refine ⟨299212243824530254281876449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199474829216353502854584299 299212243824530254281876449)
  ·
    refine ⟨224409182868397690711407337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299212243824530254281876449 224409182868397690711407337)
    ·
      refine ⟨168306887151298268033555503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224409182868397690711407337 168306887151298268033555503)
      ·
        refine ⟨252460330726947402050333255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168306887151298268033555503 252460330726947402050333255)
        ·
          refine ⟨378690496090421103075499883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252460330726947402050333255 378690496090421103075499883)
          ·
            refine ⟨568035744135631654613249825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378690496090421103075499883 568035744135631654613249825)
            ·
              refine ⟨426026808101723740959937369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568035744135631654613249825 426026808101723740959937369)
              ·
                refine ⟨319520106076292805719953027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426026808101723740959937369 319520106076292805719953027)
                ·
                  refine ⟨479280159114439208579929541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319520106076292805719953027 479280159114439208579929541)
                  ·
                    refine ⟨89865029833957351608736789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 479280159114439208579929541 89865029833957351608736789)
                    ·
                      refine ⟨4212423273466750856659537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89865029833957351608736789 4212423273466750856659537)
                      ·
                        rfl

theorem cell23_8203665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_8203665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203665 prefixEnd_8203665 := by exact prefixLift 8203665
  have htrace : WordTrace (prefixWord ++ tailWord_8203665) baseStart_8203665 baseEnd_8203665 := by
    simpa [prefixWord, tailWord_8203665, baseEnd_8203665] using wordTrace_append hprefix tailTrace_8203665
  have hstable : (prefixWord ++ tailWord_8203665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203665).length < 2 ^ (prefixWord ++ tailWord_8203665).sum := by decide
  have hdescent : baseEnd_8203665 < baseStart_8203665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203666 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_8203666 : Nat := 118140960795 + 8203666 * 2 ^ 59
def prefixEnd_8203666 : Nat := 4983230072969 + 3 ^ 40 * 8203666 * 2
def baseEnd_8203666 : Nat := 1404141262315801784249011

theorem tailTrace_8203666 : CollatzResearch.WordTrace tailWord_8203666 prefixEnd_8203666 1404141262315801784249011 := by
  unfold tailWord_8203666
  simp only [CollatzResearch.WordTrace]
  refine ⟨74803070074381657863165713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199474853531684420968441901 74803070074381657863165713)
  ·
    refine ⟨56102302555786243397374285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74803070074381657863165713 56102302555786243397374285)
    ·
      refine ⟨21038363458419841274015357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56102302555786243397374285 21038363458419841274015357)
      ·
        refine ⟨7889386296907440477755759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21038363458419841274015357 7889386296907440477755759)
        ·
          refine ⟨11834079445361160716633639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7889386296907440477755759 11834079445361160716633639)
          ·
            refine ⟨17751119168041741074950459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11834079445361160716633639 17751119168041741074950459)
            ·
              refine ⟨26626678752062611612425689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17751119168041741074950459 26626678752062611612425689)
              ·
                refine ⟨19970009064046958709319267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26626678752062611612425689 19970009064046958709319267)
                ·
                  refine ⟨29955013596070438063978901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19970009064046958709319267 29955013596070438063978901)
                  ·
                    refine ⟨1404141262315801784249011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29955013596070438063978901 1404141262315801784249011)
                    ·
                      rfl

theorem cell23_8203666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_8203666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203666 prefixEnd_8203666 := by exact prefixLift 8203666
  have htrace : WordTrace (prefixWord ++ tailWord_8203666) baseStart_8203666 baseEnd_8203666 := by
    simpa [prefixWord, tailWord_8203666, baseEnd_8203666] using wordTrace_append hprefix tailTrace_8203666
  have hstable : (prefixWord ++ tailWord_8203666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203666).length < 2 ^ (prefixWord ++ tailWord_8203666).sum := by decide
  have hdescent : baseEnd_8203666 < baseStart_8203666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203786 : List Nat := [3, 1, 2, 2, 2, 2, 3, 3, 5]
def baseStart_8203786 : Nat := 118140960795 + 8203786 * 2 ^ 59
def prefixEnd_8203786 : Nat := 4983230072969 + 3 ^ 40 * 8203786 * 2
def baseEnd_8203786 : Nat := 468053933847327209249609

theorem tailTrace_8203786 : CollatzResearch.WordTrace tailWord_8203786 prefixEnd_8203786 468053933847327209249609 := by
  unfold tailWord_8203786
  simp only [CollatzResearch.WordTrace]
  refine ⟨74804164264272972986757803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199477771371394594631354141 74804164264272972986757803)
  ·
    refine ⟨112206246396409459480136705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74804164264272972986757803 112206246396409459480136705)
    ·
      refine ⟨84154684797307094610102529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112206246396409459480136705 84154684797307094610102529)
      ·
        refine ⟨63116013597980320957576897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84154684797307094610102529 63116013597980320957576897)
        ·
          refine ⟨47337010198485240718182673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63116013597980320957576897 47337010198485240718182673)
          ·
            refine ⟨35502757648863930538637005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47337010198485240718182673 35502757648863930538637005)
            ·
              refine ⟨13313534118323973951988877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35502757648863930538637005 13313534118323973951988877)
              ·
                refine ⟨4992575294371490231995829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13313534118323973951988877 4992575294371490231995829)
                ·
                  refine ⟨468053933847327209249609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4992575294371490231995829 468053933847327209249609)
                  ·
                    rfl

theorem cell23_8203786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_8203786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203786 prefixEnd_8203786 := by exact prefixLift 8203786
  have htrace : WordTrace (prefixWord ++ tailWord_8203786) baseStart_8203786 baseEnd_8203786 := by
    simpa [prefixWord, tailWord_8203786, baseEnd_8203786] using wordTrace_append hprefix tailTrace_8203786
  have hstable : (prefixWord ++ tailWord_8203786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203786).length < 2 ^ (prefixWord ++ tailWord_8203786).sum := by decide
  have hdescent : baseEnd_8203786 < baseStart_8203786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203809 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_8203809 : Nat := 118140960795 + 8203809 * 2 ^ 59
def prefixEnd_8203809 : Nat := 4983230072969 + 3 ^ 40 * 8203809 * 2
def baseEnd_8203809 : Nat := 4212497214680998293258875

theorem tailTrace_8203809 : CollatzResearch.WordTrace tailWord_8203809 prefixEnd_8203809 4212497214680998293258875 := by
  unfold tailWord_8203809
  simp only [CollatzResearch.WordTrace]
  refine ⟨299217495936008566875118481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199478330624005711250078987 299217495936008566875118481)
  ·
    refine ⟨224413121952006425156338861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299217495936008566875118481 224413121952006425156338861)
    ·
      refine ⟨84154920732002409433627073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224413121952006425156338861 84154920732002409433627073)
      ·
        refine ⟨63116190549001807075220305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84154920732002409433627073 63116190549001807075220305)
        ·
          refine ⟨47337142911751355306415229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63116190549001807075220305 47337142911751355306415229)
          ·
            refine ⟨17751428591906758239905711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47337142911751355306415229 17751428591906758239905711)
            ·
              refine ⟨26627142887860137359858567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17751428591906758239905711 26627142887860137359858567)
              ·
                refine ⟨39940714331790206039787851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26627142887860137359858567 39940714331790206039787851)
                ·
                  refine ⟨59911071497685309059681777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39940714331790206039787851 59911071497685309059681777)
                  ·
                    refine ⟨44933303623263981794761333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59911071497685309059681777 44933303623263981794761333)
                    ·
                      refine ⟨4212497214680998293258875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44933303623263981794761333 4212497214680998293258875)
                      ·
                        rfl

theorem cell23_8203809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_8203809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203809 prefixEnd_8203809 := by exact prefixLift 8203809
  have htrace : WordTrace (prefixWord ++ tailWord_8203809) baseStart_8203809 baseEnd_8203809 := by
    simpa [prefixWord, tailWord_8203809, baseEnd_8203809] using wordTrace_append hprefix tailTrace_8203809
  have hstable : (prefixWord ++ tailWord_8203809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203809).length < 2 ^ (prefixWord ++ tailWord_8203809).sum := by decide
  have hdescent : baseEnd_8203809 < baseStart_8203809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203863 : List Nat := [1, 1, 3, 2, 2, 4, 1, 4, 1, 4]
def baseStart_8203863 : Nat := 118140960795 + 8203863 * 2 ^ 59
def prefixEnd_8203863 : Nat := 4983230072969 + 3 ^ 40 * 8203863 * 2
def baseEnd_8203863 : Nat := 1404174980878780360661209

theorem tailTrace_8203863 : CollatzResearch.WordTrace tailWord_8203863 prefixEnd_8203863 1404174980878780360661209 := by
  unfold tailWord_8203863
  simp only [CollatzResearch.WordTrace]
  refine ⟨299219465477812934097584243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199479643651875289398389495 299219465477812934097584243)
  ·
    refine ⟨448829198216719401146376365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299219465477812934097584243 448829198216719401146376365)
    ·
      refine ⟨168310949331269775429891137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448829198216719401146376365 168310949331269775429891137)
      ·
        refine ⟨126233211998452331572418353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168310949331269775429891137 126233211998452331572418353)
        ·
          refine ⟨94674908998839248679313765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126233211998452331572418353 94674908998839248679313765)
          ·
            refine ⟨17751545437282359127371331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94674908998839248679313765 17751545437282359127371331)
            ·
              refine ⟨26627318155923538691056997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17751545437282359127371331 26627318155923538691056997)
              ·
                refine ⟨4992622154235663504573187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26627318155923538691056997 4992622154235663504573187)
                ·
                  refine ⟨7488933231353495256859781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992622154235663504573187 7488933231353495256859781)
                  ·
                    refine ⟨1404174980878780360661209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488933231353495256859781 1404174980878780360661209)
                    ·
                      rfl

theorem cell23_8203863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_8203863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203863 prefixEnd_8203863 := by exact prefixLift 8203863
  have htrace : WordTrace (prefixWord ++ tailWord_8203863) baseStart_8203863 baseEnd_8203863 := by
    simpa [prefixWord, tailWord_8203863, baseEnd_8203863] using wordTrace_append hprefix tailTrace_8203863
  have hstable : (prefixWord ++ tailWord_8203863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203863).length < 2 ^ (prefixWord ++ tailWord_8203863).sum := by decide
  have hdescent : baseEnd_8203863 < baseStart_8203863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203929 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 3]
def baseStart_8203929 : Nat := 118140960795 + 8203929 * 2 ^ 59
def prefixEnd_8203929 : Nat := 4983230072969 + 3 ^ 40 * 8203929 * 2
def baseEnd_8203929 : Nat := 4212558832359537823758323

theorem tailTrace_8203929 : CollatzResearch.WordTrace tailWord_8203929 prefixEnd_8203929 4212558832359537823758323 := by
  unfold tailWord_8203929
  simp only [CollatzResearch.WordTrace]
  refine ⟨299221872695573827369486841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199481248463715884912991227 299221872695573827369486841)
  ·
    refine ⟨224416404521680370527115131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299221872695573827369486841 224416404521680370527115131)
    ·
      refine ⟨336624606782520555790672697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224416404521680370527115131 336624606782520555790672697)
      ·
        refine ⟨252468455086890416843004523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336624606782520555790672697 252468455086890416843004523)
        ·
          refine ⟨378702682630335625264506785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252468455086890416843004523 378702682630335625264506785)
          ·
            refine ⟨284027011972751718948380089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378702682630335625264506785 284027011972751718948380089)
            ·
              refine ⟨213020258979563789211285067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284027011972751718948380089 213020258979563789211285067)
              ·
                refine ⟨319530388469345683816927601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213020258979563789211285067 319530388469345683816927601)
                ·
                  refine ⟨239647791352009262862695701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319530388469345683816927601 239647791352009262862695701)
                  ·
                    refine ⟨11233490219625434196688861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 239647791352009262862695701 11233490219625434196688861)
                    ·
                      refine ⟨4212558832359537823758323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11233490219625434196688861 4212558832359537823758323)
                      ·
                        rfl

theorem cell23_8203929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_8203929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203929 prefixEnd_8203929 := by exact prefixLift 8203929
  have htrace : WordTrace (prefixWord ++ tailWord_8203929) baseStart_8203929 baseEnd_8203929 := by
    simpa [prefixWord, tailWord_8203929, baseEnd_8203929] using wordTrace_append hprefix tailTrace_8203929
  have hstable : (prefixWord ++ tailWord_8203929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203929).length < 2 ^ (prefixWord ++ tailWord_8203929).sum := by decide
  have hdescent : baseEnd_8203929 < baseStart_8203929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203936 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 1, 6]
def baseStart_8203936 : Nat := 118140960795 + 8203936 * 2 ^ 59
def prefixEnd_8203936 : Nat := 4983230072969 + 3 ^ 40 * 8203936 * 2
def baseEnd_8203936 : Nat := 1404187475574706432123597

theorem tailTrace_8203936 : CollatzResearch.WordTrace tailWord_8203936 prefixEnd_8203936 1404187475574706432123597 := by
  unfold tailWord_8203936
  simp only [CollatzResearch.WordTrace]
  refine ⟨149611064003274233782495831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199481418671032311709994441 149611064003274233782495831)
  ·
    refine ⟨224416596004911350673743747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149611064003274233782495831 224416596004911350673743747)
    ·
      refine ⟨336624894007367026010615621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224416596004911350673743747 336624894007367026010615621)
      ·
        refine ⟨63117167626381317376990429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336624894007367026010615621 63117167626381317376990429)
        ·
          refine ⟨23668937859892994016371411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63117167626381317376990429 23668937859892994016371411)
          ·
            refine ⟨35503406789839491024557117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23668937859892994016371411 35503406789839491024557117)
            ·
              refine ⟨13313777546189809134208919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35503406789839491024557117 13313777546189809134208919)
              ·
                refine ⟨19970666319284713701313379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13313777546189809134208919 19970666319284713701313379)
                ·
                  refine ⟨29955999478927070551970069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19970666319284713701313379 29955999478927070551970069)
                  ·
                    refine ⟨1404187475574706432123597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29955999478927070551970069 1404187475574706432123597)
                    ·
                      rfl

theorem cell23_8203936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_8203936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203936 prefixEnd_8203936 := by exact prefixLift 8203936
  have htrace : WordTrace (prefixWord ++ tailWord_8203936) baseStart_8203936 baseEnd_8203936 := by
    simpa [prefixWord, tailWord_8203936, baseEnd_8203936] using wordTrace_append hprefix tailTrace_8203936
  have hstable : (prefixWord ++ tailWord_8203936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203936).length < 2 ^ (prefixWord ++ tailWord_8203936).sum := by decide
  have hdescent : baseEnd_8203936 < baseStart_8203936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203939 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 6]
def baseStart_8203939 : Nat := 118140960795 + 8203939 * 2 ^ 59
def prefixEnd_8203939 : Nat := 4983230072969 + 3 ^ 40 * 8203939 * 2
def baseEnd_8203939 : Nat := 4212563967166082784633277

theorem tailTrace_8203939 : CollatzResearch.WordTrace tailWord_8203939 prefixEnd_8203939 4212563967166082784633277 := by
  unfold tailWord_8203939
  simp only [CollatzResearch.WordTrace]
  refine ⟨299222237425537599077350871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199481491617025066051567247 299222237425537599077350871)
  ·
    refine ⟨448833356138306398616026307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299222237425537599077350871 448833356138306398616026307)
    ·
      refine ⟨673250034207459597924039461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448833356138306398616026307 673250034207459597924039461)
      ·
        refine ⟨126234381413898674610757399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 673250034207459597924039461 126234381413898674610757399)
        ·
          refine ⟨189351572120848011916136099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126234381413898674610757399 189351572120848011916136099)
          ·
            refine ⟨284027358181272017874204149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189351572120848011916136099 284027358181272017874204149)
            ·
              refine ⟨26627564829494251675706639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284027358181272017874204149 26627564829494251675706639)
              ·
                refine ⟨39941347244241377513559959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26627564829494251675706639 39941347244241377513559959)
                ·
                  refine ⟨59912020866362066270339939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39941347244241377513559959 59912020866362066270339939)
                  ·
                    refine ⟨89868031299543099405509909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59912020866362066270339939 89868031299543099405509909)
                    ·
                      refine ⟨4212563967166082784633277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89868031299543099405509909 4212563967166082784633277)
                      ·
                        rfl

theorem cell23_8203939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_8203939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203939 prefixEnd_8203939 := by exact prefixLift 8203939
  have htrace : WordTrace (prefixWord ++ tailWord_8203939) baseStart_8203939 baseEnd_8203939 := by
    simpa [prefixWord, tailWord_8203939, baseEnd_8203939] using wordTrace_append hprefix tailTrace_8203939
  have hstable : (prefixWord ++ tailWord_8203939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203939).length < 2 ^ (prefixWord ++ tailWord_8203939).sum := by decide
  have hdescent : baseEnd_8203939 < baseStart_8203939 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203966 : List Nat := [4, 2, 1, 1, 2, 4, 9]
def baseStart_8203966 : Nat := 118140960795 + 8203966 * 2 ^ 59
def prefixEnd_8203966 : Nat := 4983230072969 + 3 ^ 40 * 8203966 * 2
def baseEnd_8203966 : Nat := 52007133717824125666613

theorem tailTrace_8203966 : CollatzResearch.WordTrace tailWord_8203966 prefixEnd_8203966 52007133717824125666613 := by
  unfold tailWord_8203966
  simp only [CollatzResearch.WordTrace]
  refine ⟨37402902774554972836072969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199482148130959855125722501 37402902774554972836072969)
  ·
    refine ⟨28052177080916229627054727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37402902774554972836072969 28052177080916229627054727)
    ·
      refine ⟨42078265621374344440582091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28052177080916229627054727 42078265621374344440582091)
      ·
        refine ⟨63117398432061516660873137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42078265621374344440582091 63117398432061516660873137)
        ·
          refine ⟨47338048824046137495654853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63117398432061516660873137 47338048824046137495654853)
          ·
            refine ⟨8875884154508650780435285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47338048824046137495654853 8875884154508650780435285)
            ·
              refine ⟨52007133717824125666613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8875884154508650780435285 52007133717824125666613)
              ·
                rfl

theorem cell23_8203966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 9].length) (baseStart_8203966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203966 prefixEnd_8203966 := by exact prefixLift 8203966
  have htrace : WordTrace (prefixWord ++ tailWord_8203966) baseStart_8203966 baseEnd_8203966 := by
    simpa [prefixWord, tailWord_8203966, baseEnd_8203966] using wordTrace_append hprefix tailTrace_8203966
  have hstable : (prefixWord ++ tailWord_8203966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203966).length < 2 ^ (prefixWord ++ tailWord_8203966).sum := by decide
  have hdescent : baseEnd_8203966 < baseStart_8203966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204009 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 4, 6]
def baseStart_8204009 : Nat := 118140960795 + 8204009 * 2 ^ 59
def prefixEnd_8204009 : Nat := 4983230072969 + 3 ^ 40 * 8204009 * 2
def baseEnd_8204009 : Nat := 1404199970270632503585985

theorem tailTrace_8204009 : CollatzResearch.WordTrace tailWord_8204009 prefixEnd_8204009 1404199970270632503585985 := by
  unfold tailWord_8204009
  simp only [CollatzResearch.WordTrace]
  refine ⟨299224790535284001032399081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199483193690189334021599387 299224790535284001032399081)
  ·
    refine ⟨224418592901463000774299311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299224790535284001032399081 224418592901463000774299311)
    ·
      refine ⟨336627889352194501161448967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224418592901463000774299311 336627889352194501161448967)
      ·
        refine ⟨504941834028291751742173451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336627889352194501161448967 504941834028291751742173451)
        ·
          refine ⟨757412751042437627613260177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504941834028291751742173451 757412751042437627613260177)
          ·
            refine ⟨568059563281828220709945133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757412751042437627613260177 568059563281828220709945133)
            ·
              refine ⟨213022336230685582766229425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568059563281828220709945133 213022336230685582766229425)
              ·
                refine ⟨159766752173014187074672069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213022336230685582766229425 159766752173014187074672069)
                ·
                  refine ⟨29956266032440160076501013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159766752173014187074672069 29956266032440160076501013)
                  ·
                    refine ⟨1404199970270632503585985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29956266032440160076501013 1404199970270632503585985)
                    ·
                      rfl

theorem cell23_8204009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_8204009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204009 prefixEnd_8204009 := by exact prefixLift 8204009
  have htrace : WordTrace (prefixWord ++ tailWord_8204009) baseStart_8204009 baseEnd_8204009 := by
    simpa [prefixWord, tailWord_8204009, baseEnd_8204009] using wordTrace_append hprefix tailTrace_8204009
  have hstable : (prefixWord ++ tailWord_8204009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204009).length < 2 ^ (prefixWord ++ tailWord_8204009).sum := by decide
  have hdescent : baseEnd_8204009 < baseStart_8204009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204046 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_8204046 : Nat := 118140960795 + 8204046 * 2 ^ 59
def prefixEnd_8204046 : Nat := 4983230072969 + 3 ^ 40 * 8204046 * 2
def baseEnd_8204046 : Nat := 4212618909596113865995285

theorem tailTrace_8204046 : CollatzResearch.WordTrace tailWord_8204046 prefixEnd_8204046 4212618909596113865995285 := by
  unfold tailWord_8204046
  simp only [CollatzResearch.WordTrace]
  refine ⟨37403267504518744543936999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199484093357433304234330661 37403267504518744543936999)
  ·
    refine ⟨56104901256778116815905499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37403267504518744543936999 56104901256778116815905499)
    ·
      refine ⟨84157351885167175223858249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56104901256778116815905499 84157351885167175223858249)
      ·
        refine ⟨63118013913875381417893687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84157351885167175223858249 63118013913875381417893687)
        ·
          refine ⟨94677020870813072126840531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63118013913875381417893687 94677020870813072126840531)
          ·
            refine ⟨142015531306219608190260797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94677020870813072126840531 142015531306219608190260797)
            ·
              refine ⟨53255824239832353071347799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142015531306219608190260797 53255824239832353071347799)
              ·
                refine ⟨79883736359748529607021699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53255824239832353071347799 79883736359748529607021699)
                ·
                  refine ⟨119825604539622794410532549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79883736359748529607021699 119825604539622794410532549)
                  ·
                    refine ⟨22467300851179273951974853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119825604539622794410532549 22467300851179273951974853)
                    ·
                      refine ⟨4212618909596113865995285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22467300851179273951974853 4212618909596113865995285)
                      ·
                        rfl

theorem cell23_8204046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_8204046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204046 prefixEnd_8204046 := by exact prefixLift 8204046
  have htrace : WordTrace (prefixWord ++ tailWord_8204046) baseStart_8204046 baseEnd_8204046 := by
    simpa [prefixWord, tailWord_8204046, baseEnd_8204046] using wordTrace_append hprefix tailTrace_8204046
  have hstable : (prefixWord ++ tailWord_8204046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204046).length < 2 ^ (prefixWord ++ tailWord_8204046).sum := by decide
  have hdescent : baseEnd_8204046 < baseStart_8204046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204059 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 8]
def baseStart_8204059 : Nat := 118140960795 + 8204059 * 2 ^ 59
def prefixEnd_8204059 : Nat := 4983230072969 + 3 ^ 40 * 8204059 * 2
def baseEnd_8204059 : Nat := 4212625584844622315132725

theorem tailTrace_8204059 : CollatzResearch.WordTrace tailWord_8204059 prefixEnd_8204059 4212625584844622315132725 := by
  unfold tailWord_8204059
  simp only [CollatzResearch.WordTrace]
  refine ⟨299226614185102859571719231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199484409456735239714479487 299226614185102859571719231)
  ·
    refine ⟨448839921277654289357578847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299226614185102859571719231 448839921277654289357578847)
    ·
      refine ⟨673259881916481434036368271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448839921277654289357578847 673259881916481434036368271)
      ·
        refine ⟨1009889822874722151054552407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673259881916481434036368271 1009889822874722151054552407)
        ·
          refine ⟨1514834734312083226581828611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009889822874722151054552407 1514834734312083226581828611)
          ·
            refine ⟨2272252101468124839872742917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514834734312083226581828611 2272252101468124839872742917)
            ·
              refine ⟨426047269025273407476139297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2272252101468124839872742917 426047269025273407476139297)
              ·
                refine ⟨319535451768955055607104473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426047269025273407476139297 319535451768955055607104473)
                ·
                  refine ⟨239651588826716291705328355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319535451768955055607104473 239651588826716291705328355)
                  ·
                    refine ⟨359477383240074437557992533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239651588826716291705328355 359477383240074437557992533)
                    ·
                      refine ⟨4212625584844622315132725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 359477383240074437557992533 4212625584844622315132725)
                      ·
                        rfl

theorem cell23_8204059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_8204059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204059 prefixEnd_8204059 := by exact prefixLift 8204059
  have htrace : WordTrace (prefixWord ++ tailWord_8204059) baseStart_8204059 baseEnd_8204059 := by
    simpa [prefixWord, tailWord_8204059, baseEnd_8204059] using wordTrace_append hprefix tailTrace_8204059
  have hstable : (prefixWord ++ tailWord_8204059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204059).length < 2 ^ (prefixWord ++ tailWord_8204059).sum := by decide
  have hdescent : baseEnd_8204059 < baseStart_8204059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204084 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_8204084 : Nat := 118140960795 + 8204084 * 2 ^ 59
def prefixEnd_8204084 : Nat := 4983230072969 + 3 ^ 40 * 8204084 * 2
def baseEnd_8204084 : Nat := 4212638421860984717320111

theorem tailTrace_8204084 : CollatzResearch.WordTrace tailWord_8204084 prefixEnd_8204084 4212638421860984717320111 := by
  unfold tailWord_8204084
  simp only [CollatzResearch.WordTrace]
  refine ⟨149613763005006144420689653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199485017340008192560919537 149613763005006144420689653)
  ·
    refine ⟨14026290281719326039439655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149613763005006144420689653 14026290281719326039439655)
    ·
      refine ⟨21039435422578989059159483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14026290281719326039439655 21039435422578989059159483)
      ·
        refine ⟨31559153133868483588739225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21039435422578989059159483 31559153133868483588739225)
        ·
          refine ⟨23669364850401362691554419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31559153133868483588739225 23669364850401362691554419)
          ·
            refine ⟨35504047275602044037331629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23669364850401362691554419 35504047275602044037331629)
            ·
              refine ⟨13314017728350766513999361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35504047275602044037331629 13314017728350766513999361)
              ·
                refine ⟨9985513296263074885499521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13314017728350766513999361 9985513296263074885499521)
                ·
                  refine ⟨7489134972197306164124641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9985513296263074885499521 7489134972197306164124641)
                  ·
                    refine ⟨5616851229147979623093481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7489134972197306164124641 5616851229147979623093481)
                    ·
                      refine ⟨4212638421860984717320111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5616851229147979623093481 4212638421860984717320111)
                      ·
                        rfl

theorem cell23_8204084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_8204084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204084 prefixEnd_8204084 := by exact prefixLift 8204084
  have htrace : WordTrace (prefixWord ++ tailWord_8204084) baseStart_8204084 baseEnd_8204084 := by
    simpa [prefixWord, tailWord_8204084, baseEnd_8204084] using wordTrace_append hprefix tailTrace_8204084
  have hstable : (prefixWord ++ tailWord_8204084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204084).length < 2 ^ (prefixWord ++ tailWord_8204084).sum := by decide
  have hdescent : baseEnd_8204084 < baseStart_8204084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204106 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_8204106 : Nat := 118140960795 + 8204106 * 2 ^ 59
def prefixEnd_8204106 : Nat := 4983230072969 + 3 ^ 40 * 8204106 * 2
def baseEnd_8204106 : Nat := 4212649718435383631245009

theorem tailTrace_8204106 : CollatzResearch.WordTrace tailWord_8204106 prefixEnd_8204106 4212649718435383631245009 := by
  unfold tailWord_8204106
  simp only [CollatzResearch.WordTrace]
  refine ⟨74807082103983146649670043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199485552277288391065786781 74807082103983146649670043)
  ·
    refine ⟨112210623155974719974505065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74807082103983146649670043 112210623155974719974505065)
    ·
      refine ⟨84157967366981039980878799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112210623155974719974505065 84157967366981039980878799)
      ·
        refine ⟨126236951050471559971318199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84157967366981039980878799 126236951050471559971318199)
        ·
          refine ⟨189355426575707339956977299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126236951050471559971318199 189355426575707339956977299)
          ·
            refine ⟨284033139863561009935465949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189355426575707339956977299 284033139863561009935465949)
            ·
              refine ⟨106512427448835378725799731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284033139863561009935465949 106512427448835378725799731)
              ·
                refine ⟨159768641173253068088699597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106512427448835378725799731 159768641173253068088699597)
                ·
                  refine ⟨59913240439969900533262349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159768641173253068088699597 59913240439969900533262349)
                  ·
                    refine ⟨22467465164988712699973381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59913240439969900533262349 22467465164988712699973381)
                    ·
                      refine ⟨4212649718435383631245009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22467465164988712699973381 4212649718435383631245009)
                      ·
                        rfl

theorem cell23_8204106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_8204106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204106 prefixEnd_8204106 := by exact prefixLift 8204106
  have htrace : WordTrace (prefixWord ++ tailWord_8204106) baseStart_8204106 baseEnd_8204106 := by
    simpa [prefixWord, tailWord_8204106, baseEnd_8204106] using wordTrace_append hprefix tailTrace_8204106
  have hstable : (prefixWord ++ tailWord_8204106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204106).length < 2 ^ (prefixWord ++ tailWord_8204106).sum := by decide
  have hdescent : baseEnd_8204106 < baseStart_8204106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204124 : List Nat := [2, 2, 4, 2, 3, 1, 1, 3, 5]
def baseStart_8204124 : Nat := 118140960795 + 8204124 * 2 ^ 59
def prefixEnd_8204124 : Nat := 4983230072969 + 3 ^ 40 * 8204124 * 2
def baseEnd_8204124 : Nat := 468073217898573840091103

theorem tailTrace_8204124 : CollatzResearch.WordTrace tailWord_8204124 prefixEnd_8204124 468073217898573840091103 := by
  unfold tailWord_8204124
  simp only [CollatzResearch.WordTrace]
  refine ⟨149614492464933687836417713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199485989953244917115223617 149614492464933687836417713)
  ·
    refine ⟨112210869348700265877313285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149614492464933687836417713 112210869348700265877313285)
    ·
      refine ⟨21039538002881299851996241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112210869348700265877313285 21039538002881299851996241)
      ·
        refine ⟨15779653502160974888997181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21039538002881299851996241 15779653502160974888997181)
        ·
          refine ⟨5917370063310365583373943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15779653502160974888997181 5917370063310365583373943)
          ·
            refine ⟨8876055094965548375060915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917370063310365583373943 8876055094965548375060915)
            ·
              refine ⟨13314082642448322562591373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876055094965548375060915 13314082642448322562591373)
              ·
                refine ⟨4992780990918120960971765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13314082642448322562591373 4992780990918120960971765)
                ·
                  refine ⟨468073217898573840091103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4992780990918120960971765 468073217898573840091103)
                  ·
                    rfl

theorem cell23_8204124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_8204124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204124 prefixEnd_8204124 := by exact prefixLift 8204124
  have htrace : WordTrace (prefixWord ++ tailWord_8204124) baseStart_8204124 baseEnd_8204124 := by
    simpa [prefixWord, tailWord_8204124, baseEnd_8204124] using wordTrace_append hprefix tailTrace_8204124
  have hstable : (prefixWord ++ tailWord_8204124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204124).length < 2 ^ (prefixWord ++ tailWord_8204124).sum := by decide
  have hdescent : baseEnd_8204124 < baseStart_8204124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204163 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 6]
def baseStart_8204163 : Nat := 118140960795 + 8204163 * 2 ^ 59
def prefixEnd_8204163 : Nat := 4983230072969 + 3 ^ 40 * 8204163 * 2
def baseEnd_8204163 : Nat := 468075442981409989803583

theorem tailTrace_8204163 : CollatzResearch.WordTrace tailWord_8204163 prefixEnd_8204163 468075442981409989803583 := by
  unfold tailWord_8204163
  simp only [CollatzResearch.WordTrace]
  refine ⟨299230407376726085333505143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199486938251150723555670095 299230407376726085333505143)
  ·
    refine ⟨448845611065089128000257715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299230407376726085333505143 448845611065089128000257715)
    ·
      refine ⟨673268416597633692000386573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448845611065089128000257715 673268416597633692000386573)
      ·
        refine ⟨252475656224112634500144965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673268416597633692000386573 252475656224112634500144965)
        ·
          refine ⟨47339185542021118968777181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252475656224112634500144965 47339185542021118968777181)
          ·
            refine ⟨17752194578257919613291443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47339185542021118968777181 17752194578257919613291443)
            ·
              refine ⟨26628291867386879419937165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17752194578257919613291443 26628291867386879419937165)
              ·
                refine ⟨9985609450270079782476437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26628291867386879419937165 9985609450270079782476437)
                ·
                  refine ⟨468075442981409989803583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9985609450270079782476437 468075442981409989803583)
                  ·
                    rfl

theorem cell23_8204163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 6].length) (baseStart_8204163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204163 prefixEnd_8204163 := by exact prefixLift 8204163
  have htrace : WordTrace (prefixWord ++ tailWord_8204163) baseStart_8204163 baseEnd_8204163 := by
    simpa [prefixWord, tailWord_8204163, baseEnd_8204163] using wordTrace_append hprefix tailTrace_8204163
  have hstable : (prefixWord ++ tailWord_8204163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204163).length < 2 ^ (prefixWord ++ tailWord_8204163).sum := by decide
  have hdescent : baseEnd_8204163 < baseStart_8204163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204207 : List Nat := [1, 1, 2, 1, 2, 2, 5, 4, 1, 1, 3]
def baseStart_8204207 : Nat := 118140960795 + 8204207 * 2 ^ 59
def prefixEnd_8204207 : Nat := 4983230072969 + 3 ^ 40 * 8204207 * 2
def baseEnd_8204207 : Nat := 4212701579981487736082045

theorem tailTrace_8204207 : CollatzResearch.WordTrace tailWord_8204207 prefixEnd_8204207 4212701579981487736082045 := by
  unfold tailWord_8204207
  simp only [CollatzResearch.WordTrace]
  refine ⟨299232012188566680848106875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199488008125711120565404583 299232012188566680848106875)
  ·
    refine ⟨448848018282850021272160313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299232012188566680848106875 448848018282850021272160313)
    ·
      refine ⟨336636013712137515954120235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448848018282850021272160313 336636013712137515954120235)
      ·
        refine ⟨504954020568206273931180353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336636013712137515954120235 504954020568206273931180353)
        ·
          refine ⟨378715515426154705448385265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504954020568206273931180353 378715515426154705448385265)
          ·
            refine ⟨284036636569616029086288949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378715515426154705448385265 284036636569616029086288949)
            ·
              refine ⟨26628434678401502726839589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284036636569616029086288949 26628434678401502726839589)
              ·
                refine ⟨4992831502200281761282423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26628434678401502726839589 4992831502200281761282423)
                ·
                  refine ⟨7489247253300422641923635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992831502200281761282423 7489247253300422641923635)
                  ·
                    refine ⟨11233870879950633962885453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7489247253300422641923635 11233870879950633962885453)
                    ·
                      refine ⟨4212701579981487736082045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11233870879950633962885453 4212701579981487736082045)
                      ·
                        rfl

theorem cell23_8204207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 1, 3].length) (baseStart_8204207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204207 prefixEnd_8204207 := by exact prefixLift 8204207
  have htrace : WordTrace (prefixWord ++ tailWord_8204207) baseStart_8204207 baseEnd_8204207 := by
    simpa [prefixWord, tailWord_8204207, baseEnd_8204207] using wordTrace_append hprefix tailTrace_8204207
  have hstable : (prefixWord ++ tailWord_8204207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204207).length < 2 ^ (prefixWord ++ tailWord_8204207).sum := by decide
  have hdescent : baseEnd_8204207 < baseStart_8204207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204223 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 1, 6]
def baseStart_8204223 : Nat := 118140960795 + 8204223 * 2 ^ 59
def prefixEnd_8204223 : Nat := 4983230072969 + 3 ^ 40 * 8204223 * 2
def baseEnd_8204223 : Nat := 1404236598557319891160657

theorem tailTrace_8204223 : CollatzResearch.WordTrace tailWord_8204223 prefixEnd_8204223 1404236598557319891160657 := by
  unfold tailWord_8204223
  simp only [CollatzResearch.WordTrace]
  refine ⟨299232595756508715580689323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199488397171005810387126215 299232595756508715580689323)
  ·
    refine ⟨448848893634763073371033985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299232595756508715580689323 448848893634763073371033985)
    ·
      refine ⟨336636670226072305028275489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448848893634763073371033985 336636670226072305028275489)
      ·
        refine ⟨252477502669554228771206617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336636670226072305028275489 252477502669554228771206617)
        ·
          refine ⟨189358127002165671578404963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252477502669554228771206617 189358127002165671578404963)
          ·
            refine ⟨284037190503248507367607445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189358127002165671578404963 284037190503248507367607445)
            ·
              refine ⟨13314243304839773782856599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284037190503248507367607445 13314243304839773782856599)
              ·
                refine ⟨19971364957259660674284899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314243304839773782856599 19971364957259660674284899)
                ·
                  refine ⟨29957047435889491011427349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19971364957259660674284899 29957047435889491011427349)
                  ·
                    refine ⟨1404236598557319891160657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29957047435889491011427349 1404236598557319891160657)
                    ·
                      rfl

theorem cell23_8204223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_8204223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204223 prefixEnd_8204223 := by exact prefixLift 8204223
  have htrace : WordTrace (prefixWord ++ tailWord_8204223) baseStart_8204223 baseEnd_8204223 := by
    simpa [prefixWord, tailWord_8204223, baseEnd_8204223] using wordTrace_append hprefix tailTrace_8204223
  have hstable : (prefixWord ++ tailWord_8204223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204223).length < 2 ^ (prefixWord ++ tailWord_8204223).sum := by decide
  have hdescent : baseEnd_8204223 < baseStart_8204223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204280 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_8204280 : Nat := 118140960795 + 8204280 * 2 ^ 59
def prefixEnd_8204280 : Nat := 4983230072969 + 3 ^ 40 * 8204280 * 2
def baseEnd_8204280 : Nat := 4212739064069265950469209

theorem tailTrace_8204280 : CollatzResearch.WordTrace tailWord_8204280 prefixEnd_8204280 4212739064069265950469209 := by
  unfold tailWord_8204280
  simp only [CollatzResearch.WordTrace]
  refine ⟨149617337358651107157757147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199489783144868142877009529 149617337358651107157757147)
  ·
    refine ⟨224426006037976660736635721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149617337358651107157757147 224426006037976660736635721)
    ·
      refine ⟨168319504528482495552476791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224426006037976660736635721 168319504528482495552476791)
      ·
        refine ⟨252479256792723743328715187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168319504528482495552476791 252479256792723743328715187)
        ·
          refine ⟨378718885189085614993072781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252479256792723743328715187 378718885189085614993072781)
          ·
            refine ⟨142019581945907105622402293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378718885189085614993072781 142019581945907105622402293)
            ·
              refine ⟨13314335807428791152100215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142019581945907105622402293 13314335807428791152100215)
              ·
                refine ⟨19971503711143186728150323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314335807428791152100215 19971503711143186728150323)
                ·
                  refine ⟨29957255566714780092225485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19971503711143186728150323 29957255566714780092225485)
                  ·
                    refine ⟨11233970837518042534584557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29957255566714780092225485 11233970837518042534584557)
                    ·
                      refine ⟨4212739064069265950469209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11233970837518042534584557 4212739064069265950469209)
                      ·
                        rfl

theorem cell23_8204280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_8204280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204280 prefixEnd_8204280 := by exact prefixLift 8204280
  have htrace : WordTrace (prefixWord ++ tailWord_8204280) baseStart_8204280 baseEnd_8204280 := by
    simpa [prefixWord, tailWord_8204280, baseEnd_8204280] using wordTrace_append hprefix tailTrace_8204280
  have hstable : (prefixWord ++ tailWord_8204280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204280).length < 2 ^ (prefixWord ++ tailWord_8204280).sum := by decide
  have hdescent : baseEnd_8204280 < baseStart_8204280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204293 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_8204293 : Nat := 118140960795 + 8204293 * 2 ^ 59
def prefixEnd_8204293 : Nat := 4983230072969 + 3 ^ 40 * 8204293 * 2
def baseEnd_8204293 : Nat := 4212745739317774399606649

theorem tailTrace_8204293 : CollatzResearch.WordTrace tailWord_8204293 prefixEnd_8204293 4212745739317774399606649 := by
  unfold tailWord_8204293
  simp only [CollatzResearch.WordTrace]
  refine ⟨299235148866255117535737533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199490099244170078357158355 299235148866255117535737533)
  ·
    refine ⟨112213180824845669075901575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299235148866255117535737533 112213180824845669075901575)
    ·
      refine ⟨168319771237268503613852363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112213180824845669075901575 168319771237268503613852363)
      ·
        refine ⟨252479656855902755420778545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168319771237268503613852363 252479656855902755420778545)
        ·
          refine ⟨189359742641927066565583909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252479656855902755420778545 189359742641927066565583909)
          ·
            refine ⟨35504951745361324981046983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189359742641927066565583909 35504951745361324981046983)
            ·
              refine ⟨53257427618041987471570475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35504951745361324981046983 53257427618041987471570475)
              ·
                refine ⟨79886141427062981207355713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53257427618041987471570475 79886141427062981207355713)
                ·
                  refine ⟨59914606070297235905516785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79886141427062981207355713 59914606070297235905516785)
                  ·
                    refine ⟨44935954552722926929137589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59914606070297235905516785 44935954552722926929137589)
                    ·
                      refine ⟨4212745739317774399606649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44935954552722926929137589 4212745739317774399606649)
                      ·
                        rfl

theorem cell23_8204293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_8204293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204293 prefixEnd_8204293 := by exact prefixLift 8204293
  have htrace : WordTrace (prefixWord ++ tailWord_8204293) baseStart_8204293 baseEnd_8204293 := by
    simpa [prefixWord, tailWord_8204293, baseEnd_8204293] using wordTrace_append hprefix tailTrace_8204293
  have hstable : (prefixWord ++ tailWord_8204293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204293).length < 2 ^ (prefixWord ++ tailWord_8204293).sum := by decide
  have hdescent : baseEnd_8204293 < baseStart_8204293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204298 : List Nat := [3, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_8204298 : Nat := 118140960795 + 8204298 * 2 ^ 59
def prefixEnd_8204298 : Nat := 4983230072969 + 3 ^ 40 * 8204298 * 2
def baseEnd_8204298 : Nat := 4212748306721046880044127

theorem tailTrace_8204298 : CollatzResearch.WordTrace tailWord_8204298 prefixEnd_8204298 4212748306721046880044127 := by
  unfold tailWord_8204298
  simp only [CollatzResearch.WordTrace]
  refine ⟨74808832807809250847417387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199490220820824668926446365 74808832807809250847417387)
  ·
    refine ⟨112213249211713876271126081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74808832807809250847417387 112213249211713876271126081)
    ·
      refine ⟨84159936908785407203344561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112213249211713876271126081 84159936908785407203344561)
      ·
        refine ⟨63119952681589055402508421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84159936908785407203344561 63119952681589055402508421)
        ·
          refine ⟨11834991127797947887970329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63119952681589055402508421 11834991127797947887970329)
          ·
            refine ⟨8876243345848460915977747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11834991127797947887970329 8876243345848460915977747)
            ·
              refine ⟨13314365018772691373966621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876243345848460915977747 13314365018772691373966621)
              ·
                refine ⟨4992886882039759265237483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13314365018772691373966621 4992886882039759265237483)
                ·
                  refine ⟨7489330323059638897856225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992886882039759265237483 7489330323059638897856225)
                  ·
                    refine ⟨5616997742294729173392169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7489330323059638897856225 5616997742294729173392169)
                    ·
                      refine ⟨4212748306721046880044127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5616997742294729173392169 4212748306721046880044127)
                      ·
                        rfl

theorem cell23_8204298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_8204298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204298 prefixEnd_8204298 := by exact prefixLift 8204298
  have htrace : WordTrace (prefixWord ++ tailWord_8204298) baseStart_8204298 baseEnd_8204298 := by
    simpa [prefixWord, tailWord_8204298, baseEnd_8204298] using wordTrace_append hprefix tailTrace_8204298
  have hstable : (prefixWord ++ tailWord_8204298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204298).length < 2 ^ (prefixWord ++ tailWord_8204298).sum := by decide
  have hdescent : baseEnd_8204298 < baseStart_8204298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204301 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_8204301 : Nat := 118140960795 + 8204301 * 2 ^ 59
def prefixEnd_8204301 : Nat := 4983230072969 + 3 ^ 40 * 8204301 * 2
def baseEnd_8204301 : Nat := 4212749847163010368306613

theorem tailTrace_8204301 : CollatzResearch.WordTrace tailWord_8204301 prefixEnd_8204301 4212749847163010368306613 := by
  unfold tailWord_8204301
  simp only [CollatzResearch.WordTrace]
  refine ⟨299235440650226134902028757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199490293766817423268019171 299235440650226134902028757)
  ·
    refine ⟨7013330640239675036766299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 299235440650226134902028757 7013330640239675036766299)
    ·
      refine ⟨10519995960359512555149449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7013330640239675036766299 10519995960359512555149449)
      ·
        refine ⟨7889996970269634416362087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10519995960359512555149449 7889996970269634416362087)
        ·
          refine ⟨11834995455404451624543131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7889996970269634416362087 11834995455404451624543131)
          ·
            refine ⟨17752493183106677436814697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11834995455404451624543131 17752493183106677436814697)
            ·
              refine ⟨13314369887330008077611023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17752493183106677436814697 13314369887330008077611023)
              ·
                refine ⟨19971554830995012116416535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314369887330008077611023 19971554830995012116416535)
                ·
                  refine ⟨29957332246492518174624803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19971554830995012116416535 29957332246492518174624803)
                  ·
                    refine ⟨44935998369738777261937205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29957332246492518174624803 44935998369738777261937205)
                    ·
                      refine ⟨4212749847163010368306613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44935998369738777261937205 4212749847163010368306613)
                      ·
                        rfl

theorem cell23_8204301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_8204301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204301 prefixEnd_8204301 := by exact prefixLift 8204301
  have htrace : WordTrace (prefixWord ++ tailWord_8204301) baseStart_8204301 baseEnd_8204301 := by
    simpa [prefixWord, tailWord_8204301, baseEnd_8204301] using wordTrace_append hprefix tailTrace_8204301
  have hstable : (prefixWord ++ tailWord_8204301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204301).length < 2 ^ (prefixWord ++ tailWord_8204301).sum := by decide
  have hdescent : baseEnd_8204301 < baseStart_8204301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204307 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 1, 3, 2]
def baseStart_8204307 : Nat := 118140960795 + 8204307 * 2 ^ 59
def prefixEnd_8204307 : Nat := 4983230072969 + 3 ^ 40 * 8204307 * 2
def baseEnd_8204307 : Nat := 4212752928046937344831585

theorem tailTrace_8204307 : CollatzResearch.WordTrace tailWord_8204307 prefixEnd_8204307 4212752928046937344831585 := by
  unfold tailWord_8204307
  simp only [CollatzResearch.WordTrace]
  refine ⟨299235659488204397926747175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199490439658802931951164783 299235659488204397926747175)
  ·
    refine ⟨448853489232306596890120763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299235659488204397926747175 448853489232306596890120763)
    ·
      refine ⟨673280233848459895335181145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448853489232306596890120763 673280233848459895335181145)
      ·
        refine ⟨504960175386344921501385859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673280233848459895335181145 504960175386344921501385859)
        ·
          refine ⟨757440263079517382252078789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504960175386344921501385859 757440263079517382252078789)
          ·
            refine ⟨142020049327409509172264773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 757440263079517382252078789 142020049327409509172264773)
            ·
              refine ⟨26628759248889282969799645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142020049327409509172264773 26628759248889282969799645)
              ·
                refine ⟨9985784718333481113674867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26628759248889282969799645 9985784718333481113674867)
                ·
                  refine ⟨14978677077500221670512301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9985784718333481113674867 14978677077500221670512301)
                  ·
                    refine ⟨5617003904062583126442113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14978677077500221670512301 5617003904062583126442113)
                    ·
                      refine ⟨4212752928046937344831585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617003904062583126442113 4212752928046937344831585)
                      ·
                        rfl

theorem cell23_8204307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 3, 2].length) (baseStart_8204307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204307 prefixEnd_8204307 := by exact prefixLift 8204307
  have htrace : WordTrace (prefixWord ++ tailWord_8204307) baseStart_8204307 baseEnd_8204307 := by
    simpa [prefixWord, tailWord_8204307, baseEnd_8204307] using wordTrace_append hprefix tailTrace_8204307
  have hstable : (prefixWord ++ tailWord_8204307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204307).length < 2 ^ (prefixWord ++ tailWord_8204307).sum := by decide
  have hdescent : baseEnd_8204307 < baseStart_8204307 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204323 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 5]
def baseStart_8204323 : Nat := 118140960795 + 8204323 * 2 ^ 59
def prefixEnd_8204323 : Nat := 4983230072969 + 3 ^ 40 * 8204323 * 2
def baseEnd_8204323 : Nat := 4212761143737409282231511

theorem tailTrace_8204323 : CollatzResearch.WordTrace tailWord_8204323 prefixEnd_8204323 4212761143737409282231511 := by
  unfold tailWord_8204323
  simp only [CollatzResearch.WordTrace]
  refine ⟨299236243056146432659329623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199490828704097621772886415 299236243056146432659329623)
  ·
    refine ⟨448854364584219648988994435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299236243056146432659329623 448854364584219648988994435)
    ·
      refine ⟨673281546876329473483491653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448854364584219648988994435 673281546876329473483491653)
      ·
        refine ⟨126240290039311776278154685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 673281546876329473483491653 126240290039311776278154685)
        ·
          refine ⟨47340108764741916104308007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126240290039311776278154685 47340108764741916104308007)
          ·
            refine ⟨71010163147112874156462011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47340108764741916104308007 71010163147112874156462011)
            ·
              refine ⟨106515244720669311234693017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71010163147112874156462011 106515244720669311234693017)
              ·
                refine ⟨79886433540501983426019763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106515244720669311234693017 79886433540501983426019763)
                ·
                  refine ⟨119829650310752975139029645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79886433540501983426019763 119829650310752975139029645)
                  ·
                    refine ⟨44936118866532365677136117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119829650310752975139029645 44936118866532365677136117)
                    ·
                      refine ⟨4212761143737409282231511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44936118866532365677136117 4212761143737409282231511)
                      ·
                        rfl

theorem cell23_8204323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_8204323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204323 prefixEnd_8204323 := by exact prefixLift 8204323
  have htrace : WordTrace (prefixWord ++ tailWord_8204323) baseStart_8204323 baseEnd_8204323 := by
    simpa [prefixWord, tailWord_8204323, baseEnd_8204323] using wordTrace_append hprefix tailTrace_8204323
  have hstable : (prefixWord ++ tailWord_8204323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204323).length < 2 ^ (prefixWord ++ tailWord_8204323).sum := by decide
  have hdescent : baseEnd_8204323 < baseStart_8204323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204343 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 7]
def baseStart_8204343 : Nat := 118140960795 + 8204343 * 2 ^ 59
def prefixEnd_8204343 : Nat := 4983230072969 + 3 ^ 40 * 8204343 * 2
def baseEnd_8204343 : Nat := 468085712594499911553491

theorem tailTrace_8204343 : CollatzResearch.WordTrace tailWord_8204343 prefixEnd_8204343 468085712594499911553491 := by
  unfold tailWord_8204343
  simp only [CollatzResearch.WordTrace]
  refine ⟨299236972516073976075057683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199491315010715984050038455 299236972516073976075057683)
  ·
    refine ⟨448855458774110964112586525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299236972516073976075057683 448855458774110964112586525)
    ·
      refine ⟨168320797040291611542219947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448855458774110964112586525 168320797040291611542219947)
      ·
        refine ⟨252481195560437417313329921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168320797040291611542219947 252481195560437417313329921)
        ·
          refine ⟨189360896670328062984997441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252481195560437417313329921 189360896670328062984997441)
          ·
            refine ⟨142020672502746047238748081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189360896670328062984997441 142020672502746047238748081)
            ·
              refine ⟨106515504377059535429061061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142020672502746047238748081 106515504377059535429061061)
              ·
                refine ⟨19971657070698662892948949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106515504377059535429061061 19971657070698662892948949)
                ·
                  refine ⟨468085712594499911553491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19971657070698662892948949 468085712594499911553491)
                  ·
                    rfl

theorem cell23_8204343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 7].length) (baseStart_8204343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204343 prefixEnd_8204343 := by exact prefixLift 8204343
  have htrace : WordTrace (prefixWord ++ tailWord_8204343) baseStart_8204343 baseEnd_8204343 := by
    simpa [prefixWord, tailWord_8204343, baseEnd_8204343] using wordTrace_append hprefix tailTrace_8204343
  have hstable : (prefixWord ++ tailWord_8204343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204343).length < 2 ^ (prefixWord ++ tailWord_8204343).sum := by decide
  have hdescent : baseEnd_8204343 < baseStart_8204343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204358 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_8204358 : Nat := 118140960795 + 8204358 * 2 ^ 59
def prefixEnd_8204358 : Nat := 4983230072969 + 3 ^ 40 * 8204358 * 2
def baseEnd_8204358 : Nat := 4212779115560316645293851

theorem tailTrace_8204358 : CollatzResearch.WordTrace tailWord_8204358 prefixEnd_8204358 4212779115560316645293851 := by
  unfold tailWord_8204358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9351172487844363551151679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199491679740679755757902485 9351172487844363551151679)
  ·
    refine ⟨14026758731766545326727519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9351172487844363551151679 14026758731766545326727519)
    ·
      refine ⟨21040138097649817990091279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14026758731766545326727519 21040138097649817990091279)
      ·
        refine ⟨31560207146474726985136919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21040138097649817990091279 31560207146474726985136919)
        ·
          refine ⟨47340310719712090477705379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31560207146474726985136919 47340310719712090477705379)
          ·
            refine ⟨71010466079568135716558069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47340310719712090477705379 71010466079568135716558069)
            ·
              refine ⟨6657231194959512723427319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71010466079568135716558069 6657231194959512723427319)
              ·
                refine ⟨9985846792439269085140979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657231194959512723427319 9985846792439269085140979)
                ·
                  refine ⟨14978770188658903627711469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9985846792439269085140979 14978770188658903627711469)
                  ·
                    refine ⟨5617038820747088860391801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14978770188658903627711469 5617038820747088860391801)
                    ·
                      refine ⟨4212779115560316645293851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617038820747088860391801 4212779115560316645293851)
                      ·
                        rfl

theorem cell23_8204358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_8204358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204358 prefixEnd_8204358 := by exact prefixLift 8204358
  have htrace : WordTrace (prefixWord ++ tailWord_8204358) baseStart_8204358 baseEnd_8204358 := by
    simpa [prefixWord, tailWord_8204358, baseEnd_8204358] using wordTrace_append hprefix tailTrace_8204358
  have hstable : (prefixWord ++ tailWord_8204358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204358).length < 2 ^ (prefixWord ++ tailWord_8204358).sum := by decide
  have hdescent : baseEnd_8204358 < baseStart_8204358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204374 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_8204374 : Nat := 118140960795 + 8204374 * 2 ^ 59
def prefixEnd_8204374 : Nat := 4983230072969 + 3 ^ 40 * 8204374 * 2
def baseEnd_8204374 : Nat := 4212787331250788582693777

theorem tailTrace_8204374 : CollatzResearch.WordTrace tailWord_8204374 prefixEnd_8204374 4212787331250788582693777 := by
  unfold tailWord_8204374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18702381448685104273089761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199492068785974445579624117 18702381448685104273089761)
  ·
    refine ⟨14026786086513828204817321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18702381448685104273089761 14026786086513828204817321)
    ·
      refine ⟨10520089564885371153612991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14026786086513828204817321 10520089564885371153612991)
      ·
        refine ⟨15780134347328056730419487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10520089564885371153612991 15780134347328056730419487)
        ·
          refine ⟨23670201520992085095629231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15780134347328056730419487 23670201520992085095629231)
          ·
            refine ⟨35505302281488127643443847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23670201520992085095629231 35505302281488127643443847)
            ·
              refine ⟨53257953422232191465165771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35505302281488127643443847 53257953422232191465165771)
              ·
                refine ⟨79886930133348287197748657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53257953422232191465165771 79886930133348287197748657)
                ·
                  refine ⟨59915197600011215398311493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79886930133348287197748657 59915197600011215398311493)
                  ·
                    refine ⟨11234099550002102887183405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59915197600011215398311493 11234099550002102887183405)
                    ·
                      refine ⟨4212787331250788582693777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11234099550002102887183405 4212787331250788582693777)
                      ·
                        rfl

theorem cell23_8204374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_8204374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204374 prefixEnd_8204374 := by exact prefixLift 8204374
  have htrace : WordTrace (prefixWord ++ tailWord_8204374) baseStart_8204374 baseEnd_8204374 := by
    simpa [prefixWord, tailWord_8204374, baseEnd_8204374] using wordTrace_append hprefix tailTrace_8204374
  have hstable : (prefixWord ++ tailWord_8204374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204374).length < 2 ^ (prefixWord ++ tailWord_8204374).sum := by decide
  have hdescent : baseEnd_8204374 < baseStart_8204374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204383 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_8204383 : Nat := 118140960795 + 8204383 * 2 ^ 59
def prefixEnd_8204383 : Nat := 4983230072969 + 3 ^ 40 * 8204383 * 2
def baseEnd_8204383 : Nat := 4212791952576679047481235

theorem tailTrace_8204383 : CollatzResearch.WordTrace tailWord_8204383 prefixEnd_8204383 4212791952576679047481235 := by
  unfold tailWord_8204383
  simp only [CollatzResearch.WordTrace]
  refine ⟨299238431435929062906513803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199492287623952708604342535 299238431435929062906513803)
  ·
    refine ⟨448857647153893594359770705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299238431435929062906513803 448857647153893594359770705)
    ·
      refine ⟨336643235365420195769828029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448857647153893594359770705 336643235365420195769828029)
      ·
        refine ⟨126241213262032573413685511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336643235365420195769828029 126241213262032573413685511)
        ·
          refine ⟨189361819893048860120528267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126241213262032573413685511 189361819893048860120528267)
          ·
            refine ⟨284042729839573290180792401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189361819893048860120528267 284042729839573290180792401)
            ·
              refine ⟨213032047379679967635594301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284042729839573290180792401 213032047379679967635594301)
              ·
                refine ⟨79887017767379987863347863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213032047379679967635594301 79887017767379987863347863)
                ·
                  refine ⟨119830526651069981795021795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79887017767379987863347863 119830526651069981795021795)
                  ·
                    refine ⟨179745789976604972692532693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119830526651069981795021795 179745789976604972692532693)
                    ·
                      refine ⟨4212791952576679047481235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179745789976604972692532693 4212791952576679047481235)
                      ·
                        rfl

theorem cell23_8204383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_8204383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204383 prefixEnd_8204383 := by exact prefixLift 8204383
  have htrace : WordTrace (prefixWord ++ tailWord_8204383) baseStart_8204383 baseEnd_8204383 := by
    simpa [prefixWord, tailWord_8204383, baseEnd_8204383] using wordTrace_append hprefix tailTrace_8204383
  have hstable : (prefixWord ++ tailWord_8204383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204383).length < 2 ^ (prefixWord ++ tailWord_8204383).sum := by decide
  have hdescent : baseEnd_8204383 < baseStart_8204383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204397 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_8204397 : Nat := 118140960795 + 8204397 * 2 ^ 59
def prefixEnd_8204397 : Nat := 4983230072969 + 3 ^ 40 * 8204397 * 2
def baseEnd_8204397 : Nat := 4212799141305841992706171

theorem tailTrace_8204397 : CollatzResearch.WordTrace tailWord_8204397 prefixEnd_8204397 4212799141305841992706171 := by
  unfold tailWord_8204397
  simp only [CollatzResearch.WordTrace]
  refine ⟨299238942057878343297523445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199492628038585562198348963 299238942057878343297523445)
  ·
    refine ⟨28053650817926094684142823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299238942057878343297523445 28053650817926094684142823)
    ·
      refine ⟨42080476226889142026214235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28053650817926094684142823 42080476226889142026214235)
      ·
        refine ⟨63120714340333713039321353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42080476226889142026214235 63120714340333713039321353)
        ·
          refine ⟨47340535755250284779491015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63120714340333713039321353 47340535755250284779491015)
          ·
            refine ⟨71010803632875427169236523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47340535755250284779491015 71010803632875427169236523)
            ·
              refine ⟨106516205449313140753854785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71010803632875427169236523 106516205449313140753854785)
              ·
                refine ⟨79887154086984855565391089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106516205449313140753854785 79887154086984855565391089)
                ·
                  refine ⟨59915365565238641674043317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79887154086984855565391089 59915365565238641674043317)
                  ·
                    refine ⟨5617065521741122656941561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59915365565238641674043317 5617065521741122656941561)
                    ·
                      refine ⟨4212799141305841992706171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617065521741122656941561 4212799141305841992706171)
                      ·
                        rfl

theorem cell23_8204397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_8204397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204397 prefixEnd_8204397 := by exact prefixLift 8204397
  have htrace : WordTrace (prefixWord ++ tailWord_8204397) baseStart_8204397 baseEnd_8204397 := by
    simpa [prefixWord, tailWord_8204397, baseEnd_8204397] using wordTrace_append hprefix tailTrace_8204397
  have hstable : (prefixWord ++ tailWord_8204397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204397).length < 2 ^ (prefixWord ++ tailWord_8204397).sum := by decide
  have hdescent : baseEnd_8204397 < baseStart_8204397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204407 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 2, 5]
def baseStart_8204407 : Nat := 118140960795 + 8204407 * 2 ^ 59
def prefixEnd_8204407 : Nat := 4983230072969 + 3 ^ 40 * 8204407 * 2
def baseEnd_8204407 : Nat := 1404268092037462317860375

theorem tailTrace_8204407 : CollatzResearch.WordTrace tailWord_8204407 prefixEnd_8204407 1404268092037462317860375 := by
  unfold tailWord_8204407
  simp only [CollatzResearch.WordTrace]
  refine ⟨299239306787842115005387475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199492871191894743336924983 299239306787842115005387475)
  ·
    refine ⟨448858960181763172508081213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299239306787842115005387475 448858960181763172508081213)
    ·
      refine ⟨168322110068161189690530455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448858960181763172508081213 168322110068161189690530455)
      ·
        refine ⟨252483165102241784535795683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168322110068161189690530455 252483165102241784535795683)
        ·
          refine ⟨378724747653362676803693525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252483165102241784535795683 378724747653362676803693525)
          ·
            refine ⟨8876361273125687737586567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 378724747653362676803693525 8876361273125687737586567)
            ·
              refine ⟨13314541909688531606379851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876361273125687737586567 13314541909688531606379851)
              ·
                refine ⟨19971812864532797409569777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314541909688531606379851 19971812864532797409569777)
                ·
                  refine ⟨14978859648399598057177333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19971812864532797409569777 14978859648399598057177333)
                  ·
                    refine ⟨1404268092037462317860375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14978859648399598057177333 1404268092037462317860375)
                    ·
                      rfl

theorem cell23_8204407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_8204407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204407 prefixEnd_8204407 := by exact prefixLift 8204407
  have htrace : WordTrace (prefixWord ++ tailWord_8204407) baseStart_8204407 baseEnd_8204407 := by
    simpa [prefixWord, tailWord_8204407, baseEnd_8204407] using wordTrace_append hprefix tailTrace_8204407
  have hstable : (prefixWord ++ tailWord_8204407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204407).length < 2 ^ (prefixWord ++ tailWord_8204407).sum := by decide
  have hdescent : baseEnd_8204407 < baseStart_8204407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204437 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_8204437 : Nat := 118140960795 + 8204437 * 2 ^ 59
def prefixEnd_8204437 : Nat := 4983230072969 + 3 ^ 40 * 8204437 * 2
def baseEnd_8204437 : Nat := 1404273226844007278735329

theorem tailTrace_8204437 : CollatzResearch.WordTrace tailWord_8204437 prefixEnd_8204437 1404273226844007278735329 := by
  unfold tailWord_8204437
  simp only [CollatzResearch.WordTrace]
  refine ⟨299240400977733430128979565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199493600651822286752653043 299240400977733430128979565)
  ·
    refine ⟨112215150366650036298367337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299240400977733430128979565 112215150366650036298367337)
    ·
      refine ⟨84161362774987527223775503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112215150366650036298367337 84161362774987527223775503)
      ·
        refine ⟨126242044162481290835663255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84161362774987527223775503 126242044162481290835663255)
        ·
          refine ⟨189363066243721936253494883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126242044162481290835663255 189363066243721936253494883)
          ·
            refine ⟨284044599365582904380242325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189363066243721936253494883 284044599365582904380242325)
            ·
              refine ⟨13314590595261698642823859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284044599365582904380242325 13314590595261698642823859)
              ·
                refine ⟨19971885892892547964235789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13314590595261698642823859 19971885892892547964235789)
                ·
                  refine ⟨7489457209834705486588421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19971885892892547964235789 7489457209834705486588421)
                  ·
                    refine ⟨1404273226844007278735329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7489457209834705486588421 1404273226844007278735329)
                    ·
                      rfl

theorem cell23_8204437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_8204437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204437 prefixEnd_8204437 := by exact prefixLift 8204437
  have htrace : WordTrace (prefixWord ++ tailWord_8204437) baseStart_8204437 baseEnd_8204437 := by
    simpa [prefixWord, tailWord_8204437, baseEnd_8204437] using wordTrace_append hprefix tailTrace_8204437
  have hstable : (prefixWord ++ tailWord_8204437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204437).length < 2 ^ (prefixWord ++ tailWord_8204437).sum := by decide
  have hdescent : baseEnd_8204437 < baseStart_8204437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204447 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 3]
def baseStart_8204447 : Nat := 118140960795 + 8204447 * 2 ^ 59
def prefixEnd_8204447 : Nat := 4983230072969 + 3 ^ 40 * 8204447 * 2
def baseEnd_8204447 : Nat := 4212824815338566797080941

theorem tailTrace_8204447 : CollatzResearch.WordTrace tailWord_8204447 prefixEnd_8204447 4212824815338566797080941 := by
  unfold tailWord_8204447
  simp only [CollatzResearch.WordTrace]
  refine ⟨299240765707697201836843595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199493843805131467891229063 299240765707697201836843595)
  ·
    refine ⟨448861148561545802755265393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299240765707697201836843595 448861148561545802755265393)
    ·
      refine ⟨336645861421159352066449045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448861148561545802755265393 336645861421159352066449045)
      ·
        refine ⟨15780274754116844628114799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 336645861421159352066449045 15780274754116844628114799)
        ·
          refine ⟨23670412131175266942172199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15780274754116844628114799 23670412131175266942172199)
          ·
            refine ⟨35505618196762900413258299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23670412131175266942172199 35505618196762900413258299)
            ·
              refine ⟨53258427295144350619887449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35505618196762900413258299 53258427295144350619887449)
              ·
                refine ⟨39943820471358262964915587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53258427295144350619887449 39943820471358262964915587)
                ·
                  refine ⟨59915730707037394447373381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39943820471358262964915587 59915730707037394447373381)
                  ·
                    refine ⟨11234199507569511458882509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59915730707037394447373381 11234199507569511458882509)
                    ·
                      refine ⟨4212824815338566797080941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11234199507569511458882509 4212824815338566797080941)
                      ·
                        rfl

theorem cell23_8204447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_8204447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204447 prefixEnd_8204447 := by exact prefixLift 8204447
  have htrace : WordTrace (prefixWord ++ tailWord_8204447) baseStart_8204447 baseEnd_8204447 := by
    simpa [prefixWord, tailWord_8204447, baseEnd_8204447] using wordTrace_append hprefix tailTrace_8204447
  have hstable : (prefixWord ++ tailWord_8204447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204447).length < 2 ^ (prefixWord ++ tailWord_8204447).sum := by decide
  have hdescent : baseEnd_8204447 < baseStart_8204447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204471 : List Nat := [1, 1, 3, 1, 4, 4, 1, 3, 1, 4]
def baseStart_8204471 : Nat := 118140960795 + 8204471 * 2 ^ 59
def prefixEnd_8204471 : Nat := 4983230072969 + 3 ^ 40 * 8204471 * 2
def baseEnd_8204471 : Nat := 1404279046291424901060277

theorem tailTrace_8204471 : CollatzResearch.WordTrace tailWord_8204471 prefixEnd_8204471 1404279046291424901060277 := by
  unfold tailWord_8204471
  simp only [CollatzResearch.WordTrace]
  refine ⟨299241641059610253935717267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199494427373073502623811511 299241641059610253935717267)
  ·
    refine ⟨448862461589415380903575901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299241641059610253935717267 448862461589415380903575901)
    ·
      refine ⟨168323423096030767838840963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448862461589415380903575901 168323423096030767838840963)
      ·
        refine ⟨252485134644046151758261445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168323423096030767838840963 252485134644046151758261445)
        ·
          refine ⟨47340962745758653454674021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252485134644046151758261445 47340962745758653454674021)
          ·
            refine ⟨8876430514829747522751379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47340962745758653454674021 8876430514829747522751379)
            ·
              refine ⟨13314645772244621284127069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876430514829747522751379 13314645772244621284127069)
              ·
                refine ⟨4992992164591732981547651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13314645772244621284127069 4992992164591732981547651)
                ·
                  refine ⟨7489488246887599472321477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992992164591732981547651 7489488246887599472321477)
                  ·
                    refine ⟨1404279046291424901060277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7489488246887599472321477 1404279046291424901060277)
                    ·
                      rfl

theorem cell23_8204471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_8204471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204471 prefixEnd_8204471 := by exact prefixLift 8204471
  have htrace : WordTrace (prefixWord ++ tailWord_8204471) baseStart_8204471 baseEnd_8204471 := by
    simpa [prefixWord, tailWord_8204471, baseEnd_8204471] using wordTrace_append hprefix tailTrace_8204471
  have hstable : (prefixWord ++ tailWord_8204471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204471).length < 2 ^ (prefixWord ++ tailWord_8204471).sum := by decide
  have hdescent : baseEnd_8204471 < baseStart_8204471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204481 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_8204481 : Nat := 118140960795 + 8204481 * 2 ^ 59
def prefixEnd_8204481 : Nat := 4983230072969 + 3 ^ 40 * 8204481 * 2
def baseEnd_8204481 : Nat := 4212842273680819664055785

theorem tailTrace_8204481 : CollatzResearch.WordTrace tailWord_8204481 prefixEnd_8204481 4212842273680819664055785 := by
  unfold tailWord_8204481
  simp only [CollatzResearch.WordTrace]
  refine ⟨299242005789574025643581297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199494670526382683762387531 299242005789574025643581297)
  ·
    refine ⟨224431504342180519232685973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299242005789574025643581297 224431504342180519232685973)
    ·
      refine ⟨10520226766039711839032155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224431504342180519232685973 10520226766039711839032155)
      ·
        refine ⟨15780340149059567758548233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10520226766039711839032155 15780340149059567758548233)
        ·
          refine ⟨11835255111794675818911175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15780340149059567758548233 11835255111794675818911175)
          ·
            refine ⟨17752882667692013728366763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11835255111794675818911175 17752882667692013728366763)
            ·
              refine ⟨26629324001538020592550145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17752882667692013728366763 26629324001538020592550145)
              ·
                refine ⟨19971993001153515444412609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26629324001538020592550145 19971993001153515444412609)
                ·
                  refine ⟨14978994750865136583309457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19971993001153515444412609 14978994750865136583309457)
                  ·
                    refine ⟨11234246063148852437482093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14978994750865136583309457 11234246063148852437482093)
                    ·
                      refine ⟨4212842273680819664055785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11234246063148852437482093 4212842273680819664055785)
                      ·
                        rfl

theorem cell23_8204481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_8204481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204481 prefixEnd_8204481 := by exact prefixLift 8204481
  have htrace : WordTrace (prefixWord ++ tailWord_8204481) baseStart_8204481 baseEnd_8204481 := by
    simpa [prefixWord, tailWord_8204481, baseEnd_8204481] using wordTrace_append hprefix tailTrace_8204481
  have hstable : (prefixWord ++ tailWord_8204481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204481).length < 2 ^ (prefixWord ++ tailWord_8204481).sum := by decide
  have hdescent : baseEnd_8204481 < baseStart_8204481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204501 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 6]
def baseStart_8204501 : Nat := 118140960795 + 8204501 * 2 ^ 59
def prefixEnd_8204501 : Nat := 4983230072969 + 3 ^ 40 * 8204501 * 2
def baseEnd_8204501 : Nat := 468094727032656620645077

theorem tailTrace_8204501 : CollatzResearch.WordTrace tailWord_8204501 prefixEnd_8204501 468094727032656620645077 := by
  unfold tailWord_8204501
  simp only [CollatzResearch.WordTrace]
  refine ⟨299242735249501569059309357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199495156833001046039539571 299242735249501569059309357)
  ·
    refine ⟨112216025718563088397241009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299242735249501569059309357 112216025718563088397241009)
    ·
      refine ⟨84162019288922316297930757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112216025718563088397241009 84162019288922316297930757)
      ·
        refine ⟨15780378616672934305862017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84162019288922316297930757 15780378616672934305862017)
        ·
          refine ⟨11835283962504700729396513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15780378616672934305862017 11835283962504700729396513)
          ·
            refine ⟨8876462971878525547047385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11835283962504700729396513 8876462971878525547047385)
            ·
              refine ⟨6657347228908894160285539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8876462971878525547047385 6657347228908894160285539)
              ·
                refine ⟨9986020843363341240428309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657347228908894160285539 9986020843363341240428309)
                ·
                  refine ⟨468094727032656620645077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9986020843363341240428309 468094727032656620645077)
                  ·
                    rfl

theorem cell23_8204501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_8204501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204501 prefixEnd_8204501 := by exact prefixLift 8204501
  have htrace : WordTrace (prefixWord ++ tailWord_8204501) baseStart_8204501 baseEnd_8204501 := by
    simpa [prefixWord, tailWord_8204501, baseEnd_8204501] using wordTrace_append hprefix tailTrace_8204501
  have hstable : (prefixWord ++ tailWord_8204501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204501).length < 2 ^ (prefixWord ++ tailWord_8204501).sum := by decide
  have hdescent : baseEnd_8204501 < baseStart_8204501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204527 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 1, 6]
def baseStart_8204527 : Nat := 118140960795 + 8204527 * 2 ^ 59
def prefixEnd_8204527 : Nat := 4983230072969 + 3 ^ 40 * 8204527 * 2
def baseEnd_8204527 : Nat := 1404288631263642161360191

theorem tailTrace_8204527 : CollatzResearch.WordTrace tailWord_8204527 prefixEnd_8204527 1404288631263642161360191 := by
  unfold tailWord_8204527
  simp only [CollatzResearch.WordTrace]
  refine ⟨299243683547407375499755835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199495789031604916999837223 299243683547407375499755835)
  ·
    refine ⟨448865525321111063249633753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299243683547407375499755835 448865525321111063249633753)
    ·
      refine ⟨336649143990833297437225315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448865525321111063249633753 336649143990833297437225315)
      ·
        refine ⟨504973715986249946155837973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336649143990833297437225315 504973715986249946155837973)
        ·
          refine ⟨23670642936855466226054905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 504973715986249946155837973 23670642936855466226054905)
          ·
            refine ⟨17752982202641599669541179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23670642936855466226054905 17752982202641599669541179)
            ·
              refine ⟨26629473303962399504311769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17752982202641599669541179 26629473303962399504311769)
              ·
                refine ⟨19972104977971799628233827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26629473303962399504311769 19972104977971799628233827)
                ·
                  refine ⟨29958157466957699442350741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19972104977971799628233827 29958157466957699442350741)
                  ·
                    refine ⟨1404288631263642161360191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29958157466957699442350741 1404288631263642161360191)
                    ·
                      rfl

theorem cell23_8204527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_8204527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204527 prefixEnd_8204527 := by exact prefixLift 8204527
  have htrace : WordTrace (prefixWord ++ tailWord_8204527) baseStart_8204527 baseEnd_8204527 := by
    simpa [prefixWord, tailWord_8204527, baseEnd_8204527] using wordTrace_append hprefix tailTrace_8204527
  have hstable : (prefixWord ++ tailWord_8204527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204527).length < 2 ^ (prefixWord ++ tailWord_8204527).sum := by decide
  have hdescent : baseEnd_8204527 < baseStart_8204527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204534 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_8204534 : Nat := 118140960795 + 8204534 * 2 ^ 59
def prefixEnd_8204534 : Nat := 4983230072969 + 3 ^ 40 * 8204534 * 2
def baseEnd_8204534 : Nat := 4212869488155507956693041

theorem tailTrace_8204534 : CollatzResearch.WordTrace tailWord_8204534 prefixEnd_8204534 4212869488155507956693041 := by
  unfold tailWord_8204534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18702746178648875980953791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199495959238921343796840437 18702746178648875980953791)
  ·
    refine ⟨28054119267973313971430687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18702746178648875980953791 28054119267973313971430687)
    ·
      refine ⟨42081178901959970957146031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28054119267973313971430687 42081178901959970957146031)
      ·
        refine ⟨63121768352939956435719047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42081178901959970957146031 63121768352939956435719047)
        ·
          refine ⟨94682652529409934653578571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63121768352939956435719047 94682652529409934653578571)
          ·
            refine ⟨142023978794114901980367857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94682652529409934653578571 142023978794114901980367857)
            ·
              refine ⟨106517984095586176485275893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142023978794114901980367857 106517984095586176485275893)
              ·
                refine ⟨9986061008961204045494615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106517984095586176485275893 9986061008961204045494615)
                ·
                  refine ⟨14979091513441806068241923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986061008961204045494615 14979091513441806068241923)
                  ·
                    refine ⟨22468637270162709102362885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14979091513441806068241923 22468637270162709102362885)
                    ·
                      refine ⟨4212869488155507956693041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22468637270162709102362885 4212869488155507956693041)
                      ·
                        rfl

theorem cell23_8204534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_8204534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204534 prefixEnd_8204534 := by exact prefixLift 8204534
  have htrace : WordTrace (prefixWord ++ tailWord_8204534) baseStart_8204534 baseEnd_8204534 := by
    simpa [prefixWord, tailWord_8204534, baseEnd_8204534] using wordTrace_append hprefix tailTrace_8204534
  have hstable : (prefixWord ++ tailWord_8204534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204534).length < 2 ^ (prefixWord ++ tailWord_8204534).sum := by decide
  have hdescent : baseEnd_8204534 < baseStart_8204534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204540 : List Nat := [2, 2, 2, 1, 4, 12]
def baseStart_8204540 : Nat := 118140960795 + 8204540 * 2 ^ 59
def prefixEnd_8204540 : Nat := 4983230072969 + 3 ^ 40 * 8204540 * 2
def baseEnd_8204540 : Nat := 17336924152425658161391

theorem tailTrace_8204540 : CollatzResearch.WordTrace tailWord_8204540 prefixEnd_8204540 17336924152425658161391 := by
  unfold tailWord_8204540
  simp only [CollatzResearch.WordTrace]
  refine ⟨149622078848180139359989537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199496105130906852479986049 149622078848180139359989537)
  ·
    refine ⟨112216559136135104519992153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149622078848180139359989537 112216559136135104519992153)
    ·
      refine ⟨84162419352101328389994115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112216559136135104519992153 84162419352101328389994115)
      ·
        refine ⟨126243629028151992584991173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84162419352101328389994115 126243629028151992584991173)
        ·
          refine ⟨23670680442778498609685845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126243629028151992584991173 23670680442778498609685845)
          ·
            refine ⟨17336924152425658161391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23670680442778498609685845 17336924152425658161391)
            ·
              rfl

theorem cell23_8204540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 12].length) (baseStart_8204540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204540 prefixEnd_8204540 := by exact prefixLift 8204540
  have htrace : WordTrace (prefixWord ++ tailWord_8204540) baseStart_8204540 baseEnd_8204540 := by
    simpa [prefixWord, tailWord_8204540, baseEnd_8204540] using wordTrace_append hprefix tailTrace_8204540
  have hstable : (prefixWord ++ tailWord_8204540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204540).length < 2 ^ (prefixWord ++ tailWord_8204540).sum := by decide
  have hdescent : baseEnd_8204540 < baseStart_8204540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204601 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 3]
def baseStart_8204601 : Nat := 118140960795 + 8204601 * 2 ^ 59
def prefixEnd_8204601 : Nat := 4983230072969 + 3 ^ 40 * 8204601 * 2
def baseEnd_8204601 : Nat := 4212903891359359194555233

theorem tailTrace_8204601 : CollatzResearch.WordTrace tailWord_8204601 prefixEnd_8204601 4212903891359359194555233 := by
  unfold tailWord_8204601
  simp only [CollatzResearch.WordTrace]
  refine ⟨299246382549139286137949657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199497588366092857425299771 299246382549139286137949657)
  ·
    refine ⟨224434786911854464603462243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299246382549139286137949657 224434786911854464603462243)
    ·
      refine ⟨336652180367781696905193365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224434786911854464603462243 336652180367781696905193365)
      ·
        refine ⟨15780570954739767042430939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 336652180367781696905193365 15780570954739767042430939)
        ·
          refine ⟨23670856432109650563646409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15780570954739767042430939 23670856432109650563646409)
          ·
            refine ⟨17753142324082237922734807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23670856432109650563646409 17753142324082237922734807)
            ·
              refine ⟨26629713486123356884102211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17753142324082237922734807 26629713486123356884102211)
              ·
                refine ⟨39944570229185035326153317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26629713486123356884102211 39944570229185035326153317)
                ·
                  refine ⟨7489606917972194123653747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39944570229185035326153317 7489606917972194123653747)
                  ·
                    refine ⟨11234410376958291185480621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7489606917972194123653747 11234410376958291185480621)
                    ·
                      refine ⟨4212903891359359194555233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11234410376958291185480621 4212903891359359194555233)
                      ·
                        rfl

theorem cell23_8204601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_8204601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204601 prefixEnd_8204601 := by exact prefixLift 8204601
  have htrace : WordTrace (prefixWord ++ tailWord_8204601) baseStart_8204601 baseEnd_8204601 := by
    simpa [prefixWord, tailWord_8204601, baseEnd_8204601] using wordTrace_append hprefix tailTrace_8204601
  have hstable : (prefixWord ++ tailWord_8204601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204601).length < 2 ^ (prefixWord ++ tailWord_8204601).sum := by decide
  have hdescent : baseEnd_8204601 < baseStart_8204601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204628 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_8204628 : Nat := 118140960795 + 8204628 * 2 ^ 59
def prefixEnd_8204628 : Nat := 4983230072969 + 3 ^ 40 * 8204628 * 2
def baseEnd_8204628 : Nat := 4212917755337030588917609

theorem tailTrace_8204628 : CollatzResearch.WordTrace tailWord_8204628 prefixEnd_8204628 4212917755337030588917609 := by
  unfold tailWord_8204628
  simp only [CollatzResearch.WordTrace]
  refine ⟨149623683660020734874591269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199498244880027646499455025 149623683660020734874591269)
  ·
    refine ⟨28054440686253887788985863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149623683660020734874591269 28054440686253887788985863)
    ·
      refine ⟨42081661029380831683478795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28054440686253887788985863 42081661029380831683478795)
      ·
        refine ⟨63122491544071247525218193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42081661029380831683478795 63122491544071247525218193)
        ·
          refine ⟨47341868658053435643913645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63122491544071247525218193 47341868658053435643913645)
          ·
            refine ⟨17753200746770038366467617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47341868658053435643913645 17753200746770038366467617)
            ·
              refine ⟨13314900560077528774850713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17753200746770038366467617 13314900560077528774850713)
              ·
                refine ⟨9986175420058146581138035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13314900560077528774850713 9986175420058146581138035)
                ·
                  refine ⟨14979263130087219871707053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986175420058146581138035 14979263130087219871707053)
                  ·
                    refine ⟨5617223673782707451890145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14979263130087219871707053 5617223673782707451890145)
                    ·
                      refine ⟨4212917755337030588917609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617223673782707451890145 4212917755337030588917609)
                      ·
                        rfl

theorem cell23_8204628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_8204628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204628 prefixEnd_8204628 := by exact prefixLift 8204628
  have htrace : WordTrace (prefixWord ++ tailWord_8204628) baseStart_8204628 baseEnd_8204628 := by
    simpa [prefixWord, tailWord_8204628, baseEnd_8204628] using wordTrace_append hprefix tailTrace_8204628
  have hstable : (prefixWord ++ tailWord_8204628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204628).length < 2 ^ (prefixWord ++ tailWord_8204628).sum := by decide
  have hdescent : baseEnd_8204628 < baseStart_8204628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204677 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_8204677 : Nat := 118140960795 + 8204677 * 2 ^ 59
def prefixEnd_8204677 : Nat := 4983230072969 + 3 ^ 40 * 8204677 * 2
def baseEnd_8204677 : Nat := 1404314305296366965734961

theorem tailTrace_8204677 : CollatzResearch.WordTrace tailWord_8204677 prefixEnd_8204677 1404314305296366965734961 := by
  unfold tailWord_8204677
  simp only [CollatzResearch.WordTrace]
  refine ⟨299249154496863951117716285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199499436331242634078477523 299249154496863951117716285)
  ·
    refine ⟨112218432936323981669143607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299249154496863951117716285 112218432936323981669143607)
    ·
      refine ⟨168327649404485972503715411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112218432936323981669143607 168327649404485972503715411)
      ·
        refine ⟨252491474106728958755573117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168327649404485972503715411 252491474106728958755573117)
        ·
          refine ⟨94684302790023359533339919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252491474106728958755573117 94684302790023359533339919)
          ·
            refine ⟨142026454185035039300009879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94684302790023359533339919 142026454185035039300009879)
            ·
              refine ⟨213039681277552558950014819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142026454185035039300009879 213039681277552558950014819)
              ·
                refine ⟨319559521916328838425022229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213039681277552558950014819 319559521916328838425022229)
                ·
                  refine ⟨14979352589827914301172917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319559521916328838425022229 14979352589827914301172917)
                  ·
                    refine ⟨1404314305296366965734961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14979352589827914301172917 1404314305296366965734961)
                    ·
                      rfl

theorem cell23_8204677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_8204677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204677 prefixEnd_8204677 := by exact prefixLift 8204677
  have htrace : WordTrace (prefixWord ++ tailWord_8204677) baseStart_8204677 baseEnd_8204677 := by
    simpa [prefixWord, tailWord_8204677, baseEnd_8204677] using wordTrace_append hprefix tailTrace_8204677
  have hstable : (prefixWord ++ tailWord_8204677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204677).length < 2 ^ (prefixWord ++ tailWord_8204677).sum := by decide
  have hdescent : baseEnd_8204677 < baseStart_8204677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204748 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_8204748 : Nat := 118140960795 + 8204748 * 2 ^ 59
def prefixEnd_8204748 : Nat := 4983230072969 + 3 ^ 40 * 8204748 * 2
def baseEnd_8204748 : Nat := 4212979373015570119417057

theorem tailTrace_8204748 : CollatzResearch.WordTrace tailWord_8204748 prefixEnd_8204748 4212979373015570119417057 := by
  unfold tailWord_8204748
  simp only [CollatzResearch.WordTrace]
  refine ⟨149625872039803365121775449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199501162719737820162367265 149625872039803365121775449)
  ·
    refine ⟨112219404029852523841331587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149625872039803365121775449 112219404029852523841331587)
    ·
      refine ⟨168329106044778785761997381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112219404029852523841331587 168329106044778785761997381)
      ·
        refine ⟨31561707383396022330374509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168329106044778785761997381 31561707383396022330374509)
        ·
          refine ⟨11835640268773508373890441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31561707383396022330374509 11835640268773508373890441)
          ·
            refine ⟨8876730201580131280417831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11835640268773508373890441 8876730201580131280417831)
            ·
              refine ⟨13315095302370196920626747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876730201580131280417831 13315095302370196920626747)
              ·
                refine ⟨19972642953555295380940121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13315095302370196920626747 19972642953555295380940121)
                ·
                  refine ⟨14979482215166471535705091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19972642953555295380940121 14979482215166471535705091)
                  ·
                    refine ⟨22469223322749707303557637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14979482215166471535705091 22469223322749707303557637)
                    ·
                      refine ⟨4212979373015570119417057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22469223322749707303557637 4212979373015570119417057)
                      ·
                        rfl

theorem cell23_8204748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_8204748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204748 prefixEnd_8204748 := by exact prefixLift 8204748
  have htrace : WordTrace (prefixWord ++ tailWord_8204748) baseStart_8204748 baseEnd_8204748 := by
    simpa [prefixWord, tailWord_8204748, baseEnd_8204748] using wordTrace_append hprefix tailTrace_8204748
  have hstable : (prefixWord ++ tailWord_8204748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204748).length < 2 ^ (prefixWord ++ tailWord_8204748).sum := by decide
  have hdescent : baseEnd_8204748 < baseStart_8204748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204777 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_8204777 : Nat := 118140960795 + 8204777 * 2 ^ 59
def prefixEnd_8204777 : Nat := 4983230072969 + 3 ^ 40 * 8204777 * 2
def baseEnd_8204777 : Nat := 4212994263954550505954423

theorem tailTrace_8204777 : CollatzResearch.WordTrace tailWord_8204777 prefixEnd_8204777 4212994263954550505954423 := by
  unfold tailWord_8204777
  simp only [CollatzResearch.WordTrace]
  refine ⟨299252801796501668196356585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199501867864334445464237723 299252801796501668196356585)
  ·
    refine ⟨224439601347376251147267439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299252801796501668196356585 224439601347376251147267439)
    ·
      refine ⟨336659402021064376720901159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224439601347376251147267439 336659402021064376720901159)
      ·
        refine ⟨504989103031596565081351739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336659402021064376720901159 504989103031596565081351739)
        ·
          refine ⟨757483654547394847622027609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504989103031596565081351739 757483654547394847622027609)
          ·
            refine ⟨568112740910546135716520707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757483654547394847622027609 568112740910546135716520707)
            ·
              refine ⟨852169111365819203574781061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568112740910546135716520707 852169111365819203574781061)
              ·
                refine ⟨159781708381091100670271449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 852169111365819203574781061 159781708381091100670271449)
                ·
                  refine ⟨119836281285818325502703587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159781708381091100670271449 119836281285818325502703587)
                  ·
                    refine ⟨179754421928727488254055381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119836281285818325502703587 179754421928727488254055381)
                    ·
                      refine ⟨4212994263954550505954423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179754421928727488254055381 4212994263954550505954423)
                      ·
                        rfl

theorem cell23_8204777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_8204777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204777 prefixEnd_8204777 := by exact prefixLift 8204777
  have htrace : WordTrace (prefixWord ++ tailWord_8204777) baseStart_8204777 baseEnd_8204777 := by
    simpa [prefixWord, tailWord_8204777, baseEnd_8204777] using wordTrace_append hprefix tailTrace_8204777
  have hstable : (prefixWord ++ tailWord_8204777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204777).length < 2 ^ (prefixWord ++ tailWord_8204777).sum := by decide
  have hdescent : baseEnd_8204777 < baseStart_8204777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204801 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 1, 5]
def baseStart_8204801 : Nat := 118140960795 + 8204801 * 2 ^ 59
def prefixEnd_8204801 : Nat := 4983230072969 + 3 ^ 40 * 8204801 * 2
def baseEnd_8204801 : Nat := 1404335529163419470684771

theorem tailTrace_8204801 : CollatzResearch.WordTrace tailWord_8204801 prefixEnd_8204801 1404335529163419470684771 := by
  unfold tailWord_8204801
  simp only [CollatzResearch.WordTrace]
  refine ⟨299253677148414720295230257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199502451432276480196820171 299253677148414720295230257)
  ·
    refine ⟨224440257861311040221422693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299253677148414720295230257 224440257861311040221422693)
    ·
      refine ⟨42082548348995820041516755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224440257861311040221422693 42082548348995820041516755)
      ·
        refine ⟨63123822523493730062275133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42082548348995820041516755 63123822523493730062275133)
        ·
          refine ⟨23671433446310148773353175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63123822523493730062275133 23671433446310148773353175)
          ·
            refine ⟨35507150169465223160029763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23671433446310148773353175 35507150169465223160029763)
            ·
              refine ⟨53260725254197834740044645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35507150169465223160029763 53260725254197834740044645)
              ·
                refine ⟨9986385985162094013758371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53260725254197834740044645 9986385985162094013758371)
                ·
                  refine ⟨14979578977743141020637557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986385985162094013758371 14979578977743141020637557)
                  ·
                    refine ⟨1404335529163419470684771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14979578977743141020637557 1404335529163419470684771)
                    ·
                      rfl

theorem cell23_8204801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_8204801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204801 prefixEnd_8204801 := by exact prefixLift 8204801
  have htrace : WordTrace (prefixWord ++ tailWord_8204801) baseStart_8204801 baseEnd_8204801 := by
    simpa [prefixWord, tailWord_8204801, baseEnd_8204801] using wordTrace_append hprefix tailTrace_8204801
  have hstable : (prefixWord ++ tailWord_8204801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204801).length < 2 ^ (prefixWord ++ tailWord_8204801).sum := by decide
  have hdescent : baseEnd_8204801 < baseStart_8204801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204821 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_8204821 : Nat := 118140960795 + 8204821 * 2 ^ 59
def prefixEnd_8204821 : Nat := 4983230072969 + 3 ^ 40 * 8204821 * 2
def baseEnd_8204821 : Nat := 4213016857103348333804221

theorem tailTrace_8204821 : CollatzResearch.WordTrace tailWord_8204821 prefixEnd_8204821 4213016857103348333804221 := by
  unfold tailWord_8204821
  simp only [CollatzResearch.WordTrace]
  refine ⟨299254406608342263710958317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199502937738894842473972211 299254406608342263710958317)
  ·
    refine ⟨112220402478128348891609369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299254406608342263710958317 112220402478128348891609369)
    ·
      refine ⟨84165301858596261668707027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112220402478128348891609369 84165301858596261668707027)
      ·
        refine ⟨126247952787894392503060541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84165301858596261668707027 126247952787894392503060541)
        ·
          refine ⟨47342982295460397188647703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126247952787894392503060541 47342982295460397188647703)
          ·
            refine ⟨71014473443190595782971555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47342982295460397188647703 71014473443190595782971555)
            ·
              refine ⟨106521710164785893674457333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71014473443190595782971555 106521710164785893674457333)
              ·
                refine ⟨9986410327948677531980375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106521710164785893674457333 9986410327948677531980375)
                ·
                  refine ⟨14979615491923016297970563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986410327948677531980375 14979615491923016297970563)
                  ·
                    refine ⟨22469423237884524446955845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14979615491923016297970563 22469423237884524446955845)
                    ·
                      refine ⟨4213016857103348333804221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22469423237884524446955845 4213016857103348333804221)
                      ·
                        rfl

theorem cell23_8204821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_8204821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204821 prefixEnd_8204821 := by exact prefixLift 8204821
  have htrace : WordTrace (prefixWord ++ tailWord_8204821) baseStart_8204821 baseEnd_8204821 := by
    simpa [prefixWord, tailWord_8204821, baseEnd_8204821] using wordTrace_append hprefix tailTrace_8204821
  have hstable : (prefixWord ++ tailWord_8204821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204821).length < 2 ^ (prefixWord ++ tailWord_8204821).sum := by decide
  have hdescent : baseEnd_8204821 < baseStart_8204821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204831 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 2, 4]
def baseStart_8204831 : Nat := 118140960795 + 8204831 * 2 ^ 59
def prefixEnd_8204831 : Nat := 4983230072969 + 3 ^ 40 * 8204831 * 2
def baseEnd_8204831 : Nat := 1404340663969964431559725

theorem tailTrace_8204831 : CollatzResearch.WordTrace tailWord_8204831 prefixEnd_8204831 1404340663969964431559725 := by
  unfold tailWord_8204831
  simp only [CollatzResearch.WordTrace]
  refine ⟨299254771338306035418822347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199503180892204023612548231 299254771338306035418822347)
  ·
    refine ⟨448882157007459053128233521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299254771338306035418822347 448882157007459053128233521)
    ·
      refine ⟨336661617755594289846175141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448882157007459053128233521 336661617755594289846175141)
      ·
        refine ⟨63124053329173929346157839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336661617755594289846175141 63124053329173929346157839)
        ·
          refine ⟨94686079993760894019236759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63124053329173929346157839 94686079993760894019236759)
          ·
            refine ⟨142029119990641341028855139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94686079993760894019236759 142029119990641341028855139)
            ·
              refine ⟨213043679985962011543282709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142029119990641341028855139 213043679985962011543282709)
              ·
                refine ⟨9986422499341969291091377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213043679985962011543282709 9986422499341969291091377)
                ·
                  refine ⟨7489816874506476968318533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986422499341969291091377 7489816874506476968318533)
                  ·
                    refine ⟨1404340663969964431559725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7489816874506476968318533 1404340663969964431559725)
                    ·
                      rfl

theorem cell23_8204831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 4].length) (baseStart_8204831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204831 prefixEnd_8204831 := by exact prefixLift 8204831
  have htrace : WordTrace (prefixWord ++ tailWord_8204831) baseStart_8204831 baseEnd_8204831 := by
    simpa [prefixWord, tailWord_8204831, baseEnd_8204831] using wordTrace_append hprefix tailTrace_8204831
  have hstable : (prefixWord ++ tailWord_8204831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204831).length < 2 ^ (prefixWord ++ tailWord_8204831).sum := by decide
  have hdescent : baseEnd_8204831 < baseStart_8204831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204832 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 3, 1, 3]
def baseStart_8204832 : Nat := 118140960795 + 8204832 * 2 ^ 59
def prefixEnd_8204832 : Nat := 4983230072969 + 3 ^ 40 * 8204832 * 2
def baseEnd_8204832 : Nat := 4213022505390547790766671

theorem tailTrace_8204832 : CollatzResearch.WordTrace tailWord_8204832 prefixEnd_8204832 4213022505390547790766671 := by
  unfold tailWord_8204832
  simp only [CollatzResearch.WordTrace]
  refine ⟨149627403905651206294804375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199503205207534941726405833 149627403905651206294804375)
  ·
    refine ⟨224441105858476809442206563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149627403905651206294804375 224441105858476809442206563)
    ·
      refine ⟨336661658787715214163309845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224441105858476809442206563 336661658787715214163309845)
      ·
        refine ⟨15781015255674150663905149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 336661658787715214163309845 15781015255674150663905149)
        ·
          refine ⟨5917880720877806498964431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15781015255674150663905149 5917880720877806498964431)
          ·
            refine ⟨8876821081316709748446647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917880720877806498964431 8876821081316709748446647)
            ·
              refine ⟨13315231621975064622669971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876821081316709748446647 13315231621975064622669971)
              ·
                refine ⟨19972847432962596934004957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13315231621975064622669971 19972847432962596934004957)
                ·
                  refine ⟨7489817787360973850251859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19972847432962596934004957 7489817787360973850251859)
                  ·
                    refine ⟨11234726681041460775377789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7489817787360973850251859 11234726681041460775377789)
                    ·
                      refine ⟨4213022505390547790766671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11234726681041460775377789 4213022505390547790766671)
                      ·
                        rfl

theorem cell23_8204832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_8204832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204832 prefixEnd_8204832 := by exact prefixLift 8204832
  have htrace : WordTrace (prefixWord ++ tailWord_8204832) baseStart_8204832 baseEnd_8204832 := by
    simpa [prefixWord, tailWord_8204832, baseEnd_8204832] using wordTrace_append hprefix tailTrace_8204832
  have hstable : (prefixWord ++ tailWord_8204832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204832).length < 2 ^ (prefixWord ++ tailWord_8204832).sum := by decide
  have hdescent : baseEnd_8204832 < baseStart_8204832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204848 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 2, 4]
def baseStart_8204848 : Nat := 118140960795 + 8204848 * 2 ^ 59
def prefixEnd_8204848 : Nat := 4983230072969 + 3 ^ 40 * 8204848 * 2
def baseEnd_8204848 : Nat := 1404343573693673242722199

theorem tailTrace_8204848 : CollatzResearch.WordTrace tailWord_8204848 prefixEnd_8204848 1404343573693673242722199 := by
  unfold tailWord_8204848
  simp only [CollatzResearch.WordTrace]
  refine ⟨149627695689622223661095599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199503594252829631548127465 149627695689622223661095599)
  ·
    refine ⟨224441543534433335491643399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149627695689622223661095599 224441543534433335491643399)
    ·
      refine ⟨336662315301650003237465099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224441543534433335491643399 336662315301650003237465099)
      ·
        refine ⟨504993472952475004856197649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336662315301650003237465099 504993472952475004856197649)
        ·
          refine ⟨378745104714356253642148237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504993472952475004856197649 378745104714356253642148237)
          ·
            refine ⟨142029414267883595115805589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378745104714356253642148237 142029414267883595115805589)
            ·
              refine ⟨6657628793807043521053387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142029414267883595115805589 6657628793807043521053387)
              ·
                refine ⟨9986443190710565281580081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657628793807043521053387 9986443190710565281580081)
                ·
                  refine ⟨7489832393032923961185061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986443190710565281580081 7489832393032923961185061)
                  ·
                    refine ⟨1404343573693673242722199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7489832393032923961185061 1404343573693673242722199)
                    ·
                      rfl

theorem cell23_8204848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 4].length) (baseStart_8204848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204848 prefixEnd_8204848 := by exact prefixLift 8204848
  have htrace : WordTrace (prefixWord ++ tailWord_8204848) baseStart_8204848 baseEnd_8204848 := by
    simpa [prefixWord, tailWord_8204848, baseEnd_8204848] using wordTrace_append hprefix tailTrace_8204848
  have hstable : (prefixWord ++ tailWord_8204848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204848).length < 2 ^ (prefixWord ++ tailWord_8204848).sum := by decide
  have hdescent : baseEnd_8204848 < baseStart_8204848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204852 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_8204852 : Nat := 118140960795 + 8204852 * 2 ^ 59
def prefixEnd_8204852 : Nat := 4983230072969 + 3 ^ 40 * 8204852 * 2
def baseEnd_8204852 : Nat := 1404344258334545904172193

theorem tailTrace_8204852 : CollatzResearch.WordTrace tailWord_8204852 prefixEnd_8204852 1404344258334545904172193 := by
  unfold tailWord_8204852
  simp only [CollatzResearch.WordTrace]
  refine ⟨149627768635614978002668405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199503691514153304003557873 149627768635614978002668405)
  ·
    refine ⟨14027603309588904187750163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149627768635614978002668405 14027603309588904187750163)
    ·
      refine ⟨21041404964383356281625245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14027603309588904187750163 21041404964383356281625245)
      ·
        refine ⟨7890526861643758605609467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21041404964383356281625245 7890526861643758605609467)
        ·
          refine ⟨11835790292465637908414201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7890526861643758605609467 11835790292465637908414201)
          ·
            refine ⟨8876842719349228431310651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11835790292465637908414201 8876842719349228431310651)
            ·
              refine ⟨13315264079023842646965977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876842719349228431310651 13315264079023842646965977)
              ·
                refine ⟨9986448059267881985224483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13315264079023842646965977 9986448059267881985224483)
                ·
                  refine ⟨14979672088901822977836725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986448059267881985224483 14979672088901822977836725)
                  ·
                    refine ⟨1404344258334545904172193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14979672088901822977836725 1404344258334545904172193)
                    ·
                      rfl

theorem cell23_8204852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_8204852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204852 prefixEnd_8204852 := by exact prefixLift 8204852
  have htrace : WordTrace (prefixWord ++ tailWord_8204852) baseStart_8204852 baseEnd_8204852 := by
    simpa [prefixWord, tailWord_8204852, baseEnd_8204852] using wordTrace_append hprefix tailTrace_8204852
  have hstable : (prefixWord ++ tailWord_8204852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204852).length < 2 ^ (prefixWord ++ tailWord_8204852).sum := by decide
  have hdescent : baseEnd_8204852 < baseStart_8204852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204858 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_8204858 : Nat := 118140960795 + 8204858 * 2 ^ 59
def prefixEnd_8204858 : Nat := 4983230072969 + 3 ^ 40 * 8204858 * 2
def baseEnd_8204858 : Nat := 4213035855887564689041551

theorem tailTrace_8204858 : CollatzResearch.WordTrace tailWord_8204858 prefixEnd_8204858 4213035855887564689041551 := by
  unfold tailWord_8204858
  simp only [CollatzResearch.WordTrace]
  refine ⟨74813939027302054757513807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199503837406138812686703485 74813939027302054757513807)
  ·
    refine ⟨112220908540953082136270711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74813939027302054757513807 112220908540953082136270711)
    ·
      refine ⟨168331362811429623204406067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112220908540953082136270711 168331362811429623204406067)
      ·
        refine ⟨252497044217144434806609101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168331362811429623204406067 252497044217144434806609101)
        ·
          refine ⟨94686391581429163052478413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252497044217144434806609101 94686391581429163052478413)
          ·
            refine ⟨35507396843035936144679405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94686391581429163052478413 35507396843035936144679405)
            ·
              refine ⟨13315273816138476054254777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35507396843035936144679405 13315273816138476054254777)
              ·
                refine ⟨9986455362103857040691083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13315273816138476054254777 9986455362103857040691083)
                ·
                  refine ⟨14979683043155785561036625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986455362103857040691083 14979683043155785561036625)
                  ·
                    refine ⟨11234762282366839170777469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14979683043155785561036625 11234762282366839170777469)
                    ·
                      refine ⟨4213035855887564689041551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11234762282366839170777469 4213035855887564689041551)
                      ·
                        rfl

theorem cell23_8204858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_8204858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204858 prefixEnd_8204858 := by exact prefixLift 8204858
  have htrace : WordTrace (prefixWord ++ tailWord_8204858) baseStart_8204858 baseEnd_8204858 := by
    simpa [prefixWord, tailWord_8204858, baseEnd_8204858] using wordTrace_append hprefix tailTrace_8204858
  have hstable : (prefixWord ++ tailWord_8204858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204858).length < 2 ^ (prefixWord ++ tailWord_8204858).sum := by decide
  have hdescent : baseEnd_8204858 < baseStart_8204858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204871 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_8204871 : Nat := 118140960795 + 8204871 * 2 ^ 59
def prefixEnd_8204871 : Nat := 4983230072969 + 3 ^ 40 * 8204871 * 2
def baseEnd_8204871 : Nat := 4213042531136073138178991

theorem tailTrace_8204871 : CollatzResearch.WordTrace tailWord_8204871 prefixEnd_8204871 4213042531136073138178991 := by
  unfold tailWord_8204871
  simp only [CollatzResearch.WordTrace]
  refine ⟨299256230258161122250278467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199504153505440748166852311 299256230258161122250278467)
  ·
    refine ⟨448884345387241683375417701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299256230258161122250278467 448884345387241683375417701)
    ·
      refine ⟨84165814760107815632890819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448884345387241683375417701 84165814760107815632890819)
      ·
        refine ⟨126248722140161723449336229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84165814760107815632890819 126248722140161723449336229)
        ·
          refine ⟨23671635401280323146750543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126248722140161723449336229 23671635401280323146750543)
          ·
            refine ⟨35507453101920484720125815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23671635401280323146750543 35507453101920484720125815)
            ·
              refine ⟨53261179652880727080188723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35507453101920484720125815 53261179652880727080188723)
              ·
                refine ⟨79891769479321090620283085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53261179652880727080188723 79891769479321090620283085)
                ·
                  refine ⟨29959413554745408982606157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79891769479321090620283085 29959413554745408982606157)
                  ·
                    refine ⟨11234780083029528368477309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29959413554745408982606157 11234780083029528368477309)
                    ·
                      refine ⟨4213042531136073138178991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11234780083029528368477309 4213042531136073138178991)
                      ·
                        rfl

theorem cell23_8204871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_8204871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204871 prefixEnd_8204871 := by exact prefixLift 8204871
  have htrace : WordTrace (prefixWord ++ tailWord_8204871) baseStart_8204871 baseEnd_8204871 := by
    simpa [prefixWord, tailWord_8204871, baseEnd_8204871] using wordTrace_append hprefix tailTrace_8204871
  have hstable : (prefixWord ++ tailWord_8204871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204871).length < 2 ^ (prefixWord ++ tailWord_8204871).sum := by decide
  have hdescent : baseEnd_8204871 < baseStart_8204871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204888 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_8204888 : Nat := 118140960795 + 8204888 * 2 ^ 59
def prefixEnd_8204888 : Nat := 4983230072969 + 3 ^ 40 * 8204888 * 2
def baseEnd_8204888 : Nat := 4213051260307199571666413

theorem tailTrace_8204888 : CollatzResearch.WordTrace tailWord_8204888 prefixEnd_8204888 4213051260307199571666413 := by
  unfold tailWord_8204888
  simp only [CollatzResearch.WordTrace]
  refine ⟨149628425149549767076823659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199504566866066356102431545 149628425149549767076823659)
  ·
    refine ⟨224442637724324650615235489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149628425149549767076823659 224442637724324650615235489)
    ·
      refine ⟨168331978293243487961426617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224442637724324650615235489 168331978293243487961426617)
      ·
        refine ⟨126248983719932615971069963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168331978293243487961426617 126248983719932615971069963)
        ·
          refine ⟨189373475579898923956604945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126248983719932615971069963 189373475579898923956604945)
          ·
            refine ⟨142030106684924192967453709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189373475579898923956604945 142030106684924192967453709)
            ·
              refine ⟨53261290006846572362795141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142030106684924192967453709 53261290006846572362795141)
              ·
                refine ⟨9986491876283732318024089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53261290006846572362795141 9986491876283732318024089)
                ·
                  refine ⟨7489868907212799238518067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986491876283732318024089 7489868907212799238518067)
                  ·
                    refine ⟨11234803360819198857777101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7489868907212799238518067 11234803360819198857777101)
                    ·
                      refine ⟨4213051260307199571666413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11234803360819198857777101 4213051260307199571666413)
                      ·
                        rfl

theorem cell23_8204888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_8204888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204888 prefixEnd_8204888 := by exact prefixLift 8204888
  have htrace : WordTrace (prefixWord ++ tailWord_8204888) baseStart_8204888 baseEnd_8204888 := by
    simpa [prefixWord, tailWord_8204888, baseEnd_8204888] using wordTrace_append hprefix tailTrace_8204888
  have hstable : (prefixWord ++ tailWord_8204888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204888).length < 2 ^ (prefixWord ++ tailWord_8204888).sum := by decide
  have hdescent : baseEnd_8204888 < baseStart_8204888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204928 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 1, 4, 2]
def baseStart_8204928 : Nat := 118140960795 + 8204928 * 2 ^ 59
def prefixEnd_8204928 : Nat := 4983230072969 + 3 ^ 40 * 8204928 * 2
def baseEnd_8204928 : Nat := 4213071799533379415166229

theorem tailTrace_8204928 : CollatzResearch.WordTrace tailWord_8204928 prefixEnd_8204928 4213071799533379415166229 := by
  unfold tailWord_8204928
  simp only [CollatzResearch.WordTrace]
  refine ⟨149629154609477310492551719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199505539479303080656735625 149629154609477310492551719)
  ·
    refine ⟨224443731914215965738827579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149629154609477310492551719 224443731914215965738827579)
    ·
      refine ⟨336665597871323948608241369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224443731914215965738827579 336665597871323948608241369)
      ·
        refine ⟨252499198403492961456181027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336665597871323948608241369 252499198403492961456181027)
        ·
          refine ⟨378748797605239442184271541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252499198403492961456181027 378748797605239442184271541)
          ·
            refine ⟨35507699775491197704775457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 378748797605239442184271541 35507699775491197704775457)
            ·
              refine ⟨26630774831618398278581593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35507699775491197704775457 26630774831618398278581593)
              ·
                refine ⟨19973081123713798708936195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26630774831618398278581593 19973081123713798708936195)
                ·
                  refine ⟨29959621685570698063404293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19973081123713798708936195 29959621685570698063404293)
                  ·
                    refine ⟨5617429066044505886888305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29959621685570698063404293 5617429066044505886888305)
                    ·
                      refine ⟨4213071799533379415166229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617429066044505886888305 4213071799533379415166229)
                      ·
                        rfl

theorem cell23_8204928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_8204928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204928 prefixEnd_8204928 := by exact prefixLift 8204928
  have htrace : WordTrace (prefixWord ++ tailWord_8204928) baseStart_8204928 baseEnd_8204928 := by
    simpa [prefixWord, tailWord_8204928, baseEnd_8204928] using wordTrace_append hprefix tailTrace_8204928
  have hstable : (prefixWord ++ tailWord_8204928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204928).length < 2 ^ (prefixWord ++ tailWord_8204928).sum := by decide
  have hdescent : baseEnd_8204928 < baseStart_8204928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204932 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_8204932 : Nat := 118140960795 + 8204932 * 2 ^ 59
def prefixEnd_8204932 : Nat := 4983230072969 + 3 ^ 40 * 8204932 * 2
def baseEnd_8204932 : Nat := 4213073853455997399516211

theorem tailTrace_8204932 : CollatzResearch.WordTrace tailWord_8204932 prefixEnd_8204932 4213073853455997399516211 := by
  unfold tailWord_8204932
  simp only [CollatzResearch.WordTrace]
  refine ⟨149629227555470064834124525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199505636740626753112166033 149629227555470064834124525)
  ·
    refine ⟨56110960333301274312796697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149629227555470064834124525 56110960333301274312796697)
    ·
      refine ⟨42083220249975955734597523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56110960333301274312796697 42083220249975955734597523)
      ·
        refine ⟨63124830374963933601896285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42083220249975955734597523 63124830374963933601896285)
        ·
          refine ⟨23671811390611475100711107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63124830374963933601896285 23671811390611475100711107)
          ·
            refine ⟨35507717085917212651066661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23671811390611475100711107 35507717085917212651066661)
            ·
              refine ⟨6657696953609477372074999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35507717085917212651066661 6657696953609477372074999)
              ·
                refine ⟨9986545430414216058112499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657696953609477372074999 9986545430414216058112499)
                ·
                  refine ⟨14979818145621324087168749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986545430414216058112499 14979818145621324087168749)
                  ·
                    refine ⟨5617431804607996532688281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14979818145621324087168749 5617431804607996532688281)
                    ·
                      refine ⟨4213073853455997399516211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617431804607996532688281 4213073853455997399516211)
                      ·
                        rfl

theorem cell23_8204932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_8204932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204932 prefixEnd_8204932 := by exact prefixLift 8204932
  have htrace : WordTrace (prefixWord ++ tailWord_8204932) baseStart_8204932 baseEnd_8204932 := by
    simpa [prefixWord, tailWord_8204932, baseEnd_8204932] using wordTrace_append hprefix tailTrace_8204932
  have hstable : (prefixWord ++ tailWord_8204932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204932).length < 2 ^ (prefixWord ++ tailWord_8204932).sum := by decide
  have hdescent : baseEnd_8204932 < baseStart_8204932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204951 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 7]
def baseStart_8204951 : Nat := 118140960795 + 8204951 * 2 ^ 59
def prefixEnd_8204951 : Nat := 4983230072969 + 3 ^ 40 * 8204951 * 2
def baseEnd_8204951 : Nat := 468120401065381425019847

theorem tailTrace_8204951 : CollatzResearch.WordTrace tailWord_8204951 prefixEnd_8204951 468120401065381425019847 := by
  unfold tailWord_8204951
  simp only [CollatzResearch.WordTrace]
  refine ⟨299259148097871295913190707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199506098731914197275460471 299259148097871295913190707)
  ·
    refine ⟨448888722146806943869786061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299259148097871295913190707 448888722146806943869786061)
    ·
      refine ⟨168333270805052603951169773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448888722146806943869786061 168333270805052603951169773)
      ·
        refine ⟨63124976551894726481688665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168333270805052603951169773 63124976551894726481688665)
        ·
          refine ⟨47343732413921044861266499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63124976551894726481688665 47343732413921044861266499)
          ·
            refine ⟨71015598620881567291899749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47343732413921044861266499 71015598620881567291899749)
            ·
              refine ⟨13315424741415293867231203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71015598620881567291899749 13315424741415293867231203)
              ·
                refine ⟨19973137112122940800846805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13315424741415293867231203 19973137112122940800846805)
                ·
                  refine ⟨468120401065381425019847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19973137112122940800846805 468120401065381425019847)
                  ·
                    rfl

theorem cell23_8204951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 7].length) (baseStart_8204951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204951 prefixEnd_8204951 := by exact prefixLift 8204951
  have htrace : WordTrace (prefixWord ++ tailWord_8204951) baseStart_8204951 baseEnd_8204951 := by
    simpa [prefixWord, tailWord_8204951, baseEnd_8204951] using wordTrace_append hprefix tailTrace_8204951
  have hstable : (prefixWord ++ tailWord_8204951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204951).length < 2 ^ (prefixWord ++ tailWord_8204951).sum := by decide
  have hdescent : baseEnd_8204951 < baseStart_8204951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204958 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_8204958 : Nat := 118140960795 + 8204958 * 2 ^ 59
def prefixEnd_8204958 : Nat := 4983230072969 + 3 ^ 40 * 8204958 * 2
def baseEnd_8204958 : Nat := 4213087203953014297791091

theorem tailTrace_8204958 : CollatzResearch.WordTrace tailWord_8204958 prefixEnd_8204958 4213087203953014297791091 := by
  unfold tailWord_8204958
  simp only [CollatzResearch.WordTrace]
  refine ⟨37407425426105742013586941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199506268939230624072463685 37407425426105742013586941)
  ·
    refine ⟨14027784534789653255095103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37407425426105742013586941 14027784534789653255095103)
    ·
      refine ⟨21041676802184479882642655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14027784534789653255095103 21041676802184479882642655)
      ·
        refine ⟨31562515203276719823963983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21041676802184479882642655 31562515203276719823963983)
        ·
          refine ⟨47343772804915079735945975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31562515203276719823963983 47343772804915079735945975)
          ·
            refine ⟨71015659207372619603918963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47343772804915079735945975 71015659207372619603918963)
            ·
              refine ⟨106523488811058929405878445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71015659207372619603918963 106523488811058929405878445)
              ·
                refine ⟨39946308304147098527204417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106523488811058929405878445 39946308304147098527204417)
                ·
                  refine ⟨29959731228110323895403313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39946308304147098527204417 29959731228110323895403313)
                  ·
                    refine ⟨22469798421082742921552485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29959731228110323895403313 22469798421082742921552485)
                    ·
                      refine ⟨4213087203953014297791091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22469798421082742921552485 4213087203953014297791091)
                      ·
                        rfl

theorem cell23_8204958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_8204958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8204958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8204958 prefixEnd_8204958 := by exact prefixLift 8204958
  have htrace : WordTrace (prefixWord ++ tailWord_8204958) baseStart_8204958 baseEnd_8204958 := by
    simpa [prefixWord, tailWord_8204958, baseEnd_8204958] using wordTrace_append hprefix tailTrace_8204958
  have hstable : (prefixWord ++ tailWord_8204958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204958).length < 2 ^ (prefixWord ++ tailWord_8204958).sum := by decide
  have hdescent : baseEnd_8204958 < baseStart_8204958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205013 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_8205013 : Nat := 118140960795 + 8205013 * 2 ^ 59
def prefixEnd_8205013 : Nat := 4983230072969 + 3 ^ 40 * 8205013 * 2
def baseEnd_8205013 : Nat := 4213115445389011582603339

theorem tailTrace_8205013 : CollatzResearch.WordTrace tailWord_8205013 prefixEnd_8205013 4213115445389011582603339 := by
  unfold tailWord_8205013
  simp only [CollatzResearch.WordTrace]
  refine ⟨299261409423646680501947693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199507606282431120334631795 299261409423646680501947693)
  ·
    refine ⟨112223028533867505188230385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299261409423646680501947693 112223028533867505188230385)
    ·
      refine ⟨84167271400400628891172789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112223028533867505188230385 84167271400400628891172789)
      ·
        refine ⟨7890681693787558958547449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84167271400400628891172789 7890681693787558958547449)
        ·
          refine ⟨5918011270340669218910587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7890681693787558958547449 5918011270340669218910587)
          ·
            refine ⟨8877016905511003828365881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918011270340669218910587 8877016905511003828365881)
            ·
              refine ⟨6657762679133252871274411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8877016905511003828365881 6657762679133252871274411)
              ·
                refine ⟨9986644018699879306911617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657762679133252871274411 9986644018699879306911617)
                ·
                  refine ⟨7489983014024909480183713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986644018699879306911617 7489983014024909480183713)
                  ·
                    refine ⟨5617487260518682110137785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7489983014024909480183713 5617487260518682110137785)
                    ·
                      refine ⟨4213115445389011582603339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617487260518682110137785 4213115445389011582603339)
                      ·
                        rfl

theorem cell23_8205013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_8205013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205013 prefixEnd_8205013 := by exact prefixLift 8205013
  have htrace : WordTrace (prefixWord ++ tailWord_8205013) baseStart_8205013 baseEnd_8205013 := by
    simpa [prefixWord, tailWord_8205013, baseEnd_8205013] using wordTrace_append hprefix tailTrace_8205013
  have hstable : (prefixWord ++ tailWord_8205013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205013).length < 2 ^ (prefixWord ++ tailWord_8205013).sum := by decide
  have hdescent : baseEnd_8205013 < baseStart_8205013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205018 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2]
def baseStart_8205018 : Nat := 118140960795 + 8205018 * 2 ^ 59
def prefixEnd_8205018 : Nat := 4983230072969 + 3 ^ 40 * 8205018 * 2
def baseEnd_8205018 : Nat := 4213118012792284063040815

theorem tailTrace_8205018 : CollatzResearch.WordTrace tailWord_8205018 prefixEnd_8205018 4213118012792284063040815 := by
  unfold tailWord_8205018
  simp only [CollatzResearch.WordTrace]
  refine ⟨74815397947157141588969927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199507727859085710903919805 74815397947157141588969927)
  ·
    refine ⟨112223096920735712383454891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74815397947157141588969927 112223096920735712383454891)
    ·
      refine ⟨168334645381103568575182337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112223096920735712383454891 168334645381103568575182337)
      ·
        refine ⟨126250984035827676431386753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168334645381103568575182337 126250984035827676431386753)
        ·
          refine ⟨94688238026870757323540065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126250984035827676431386753 94688238026870757323540065)
          ·
            refine ⟨71016178520153067992655049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94688238026870757323540065 71016178520153067992655049)
            ·
              refine ⟨53262133890114800994491287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71016178520153067992655049 53262133890114800994491287)
              ·
                refine ⟨79893200835172201491736931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53262133890114800994491287 79893200835172201491736931)
                ·
                  refine ⟨119839801252758302237605397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79893200835172201491736931 119839801252758302237605397)
                  ·
                    refine ⟨5617490683723045417387753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119839801252758302237605397 5617490683723045417387753)
                    ·
                      refine ⟨4213118012792284063040815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617490683723045417387753 4213118012792284063040815)
                      ·
                        rfl

theorem cell23_8205018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_8205018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205018 prefixEnd_8205018 := by exact prefixLift 8205018
  have htrace : WordTrace (prefixWord ++ tailWord_8205018) baseStart_8205018 baseEnd_8205018 := by
    simpa [prefixWord, tailWord_8205018, baseEnd_8205018] using wordTrace_append hprefix tailTrace_8205018
  have hstable : (prefixWord ++ tailWord_8205018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205018).length < 2 ^ (prefixWord ++ tailWord_8205018).sum := by decide
  have hdescent : baseEnd_8205018 < baseStart_8205018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205051 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 3]
def baseStart_8205051 : Nat := 118140960795 + 8205051 * 2 ^ 59
def prefixEnd_8205051 : Nat := 4983230072969 + 3 ^ 40 * 8205051 * 2
def baseEnd_8205051 : Nat := 4213134957653882433928163

theorem tailTrace_8205051 : CollatzResearch.WordTrace tailWord_8205051 prefixEnd_8205051 4213134957653882433928163 := by
  unfold tailWord_8205051
  simp only [CollatzResearch.WordTrace]
  refine ⟨299262795397509012991831007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199508530265006008661220671 299262795397509012991831007)
  ·
    refine ⟨448894193096263519487746511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299262795397509012991831007 448894193096263519487746511)
    ·
      refine ⟨673341289644395279231619767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448894193096263519487746511 673341289644395279231619767)
      ·
        refine ⟨1010011934466592918847429651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673341289644395279231619767 1010011934466592918847429651)
        ·
          refine ⟨1515017901699889378271144477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010011934466592918847429651 1515017901699889378271144477)
          ·
            refine ⟨568131713137458516851679179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1515017901699889378271144477 568131713137458516851679179)
            ·
              refine ⟨852197569706187775277518769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568131713137458516851679179 852197569706187775277518769)
              ·
                refine ⟨639148177279640831458139077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852197569706187775277518769 639148177279640831458139077)
                ·
                  refine ⟨119840283239932655898401077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639148177279640831458139077 119840283239932655898401077)
                  ·
                    refine ⟨11235026553743686490475101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119840283239932655898401077 11235026553743686490475101)
                    ·
                      refine ⟨4213134957653882433928163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11235026553743686490475101 4213134957653882433928163)
                      ·
                        rfl

theorem cell23_8205051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 3].length) (baseStart_8205051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205051 prefixEnd_8205051 := by exact prefixLift 8205051
  have htrace : WordTrace (prefixWord ++ tailWord_8205051) baseStart_8205051 baseEnd_8205051 := by
    simpa [prefixWord, tailWord_8205051, baseEnd_8205051] using wordTrace_append hprefix tailTrace_8205051
  have hstable : (prefixWord ++ tailWord_8205051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205051).length < 2 ^ (prefixWord ++ tailWord_8205051).sum := by decide
  have hdescent : baseEnd_8205051 < baseStart_8205051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205071 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 5, 5]
def baseStart_8205071 : Nat := 118140960795 + 8205071 * 2 ^ 59
def prefixEnd_8205071 : Nat := 4983230072969 + 3 ^ 40 * 8205071 * 2
def baseEnd_8205071 : Nat := 1404381742422324118559357

theorem tailTrace_8205071 : CollatzResearch.WordTrace tailWord_8205071 prefixEnd_8205071 1404381742422324118559357 := by
  unfold tailWord_8205071
  simp only [CollatzResearch.WordTrace]
  refine ⟨299263524857436556407559067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199509016571624370938372711 299263524857436556407559067)
  ·
    refine ⟨448895287286154834611338601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299263524857436556407559067 448895287286154834611338601)
    ·
      refine ⟨336671465464616125958503951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448895287286154834611338601 336671465464616125958503951)
      ·
        refine ⟨505007198196924188937755927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336671465464616125958503951 505007198196924188937755927)
        ·
          refine ⟨757510797295386283406633891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505007198196924188937755927 757510797295386283406633891)
          ·
            refine ⟨1136266195943079425109950837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757510797295386283406633891 1136266195943079425109950837)
            ·
              refine ⟨106524955869663696104057891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1136266195943079425109950837 106524955869663696104057891)
              ·
                refine ⟨159787433804495544156086837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106524955869663696104057891 159787433804495544156086837)
                ·
                  refine ⟨14980071919171457264633141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159787433804495544156086837 14980071919171457264633141)
                  ·
                    refine ⟨1404381742422324118559357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14980071919171457264633141 1404381742422324118559357)
                    ·
                      rfl

theorem cell23_8205071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_8205071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205071 prefixEnd_8205071 := by exact prefixLift 8205071
  have htrace : WordTrace (prefixWord ++ tailWord_8205071) baseStart_8205071 baseEnd_8205071 := by
    simpa [prefixWord, tailWord_8205071, baseEnd_8205071] using wordTrace_append hprefix tailTrace_8205071
  have hstable : (prefixWord ++ tailWord_8205071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205071).length < 2 ^ (prefixWord ++ tailWord_8205071).sum := by decide
  have hdescent : baseEnd_8205071 < baseStart_8205071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205088 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 3, 5]
def baseStart_8205088 : Nat := 118140960795 + 8205088 * 2 ^ 59
def prefixEnd_8205088 : Nat := 4983230072969 + 3 ^ 40 * 8205088 * 2
def baseEnd_8205088 : Nat := 1404384652146032929721831

theorem tailTrace_8205088 : CollatzResearch.WordTrace tailWord_8205088 prefixEnd_8205088 1404384652146032929721831 := by
  unfold tailWord_8205088
  simp only [CollatzResearch.WordTrace]
  refine ⟨149632072449187484155463959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199509429932249978873951945 149632072449187484155463959)
  ·
    refine ⟨224448108673781226233195939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149632072449187484155463959 224448108673781226233195939)
    ·
      refine ⟨336672163010671839349793909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224448108673781226233195939 336672163010671839349793909)
      ·
        refine ⟨31563015282250484939043179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336672163010671839349793909 31563015282250484939043179)
        ·
          refine ⟨47344522923375727408564769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31563015282250484939043179 47344522923375727408564769)
          ·
            refine ⟨35508392192531795556423577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47344522923375727408564769 35508392192531795556423577)
            ·
              refine ⟨26631294144398846667317683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35508392192531795556423577 26631294144398846667317683)
              ·
                refine ⟨39946941216598270000976525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26631294144398846667317683 39946941216598270000976525)
                ·
                  refine ⟨14980102956224351250366197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39946941216598270000976525 14980102956224351250366197)
                  ·
                    refine ⟨1404384652146032929721831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14980102956224351250366197 1404384652146032929721831)
                    ·
                      rfl

theorem cell23_8205088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_8205088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205088 prefixEnd_8205088 := by exact prefixLift 8205088
  have htrace : WordTrace (prefixWord ++ tailWord_8205088) baseStart_8205088 baseEnd_8205088 := by
    simpa [prefixWord, tailWord_8205088, baseEnd_8205088] using wordTrace_append hprefix tailTrace_8205088
  have hstable : (prefixWord ++ tailWord_8205088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205088).length < 2 ^ (prefixWord ++ tailWord_8205088).sum := by decide
  have hdescent : baseEnd_8205088 < baseStart_8205088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205128 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_8205128 : Nat := 118140960795 + 8205128 * 2 ^ 59
def prefixEnd_8205128 : Nat := 4983230072969 + 3 ^ 40 * 8205128 * 2
def baseEnd_8205128 : Nat := 4213174495664278632665309

theorem tailTrace_8205128 : CollatzResearch.WordTrace tailWord_8205128 prefixEnd_8205128 4213174495664278632665309 := by
  unfold tailWord_8205128
  simp only [CollatzResearch.WordTrace]
  refine ⟨149632801909115027571192019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199510402545486703428256025 149632801909115027571192019)
  ·
    refine ⟨224449202863672541356788029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149632801909115027571192019 224449202863672541356788029)
    ·
      refine ⟨84168451073877203008795511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224449202863672541356788029 84168451073877203008795511)
      ·
        refine ⟨126252676610815804513193267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84168451073877203008795511 126252676610815804513193267)
        ·
          refine ⟨189379014916223706769789901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126252676610815804513193267 189379014916223706769789901)
          ·
            refine ⟨71017130593583890038671213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189379014916223706769789901 71017130593583890038671213)
            ·
              refine ⟨26631423972593958764501705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71017130593583890038671213 26631423972593958764501705)
              ·
                refine ⟨19973567979445469073376279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26631423972593958764501705 19973567979445469073376279)
                ·
                  refine ⟨29960351969168203610064419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19973567979445469073376279 29960351969168203610064419)
                  ·
                    refine ⟨44940527953752305415096629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29960351969168203610064419 44940527953752305415096629)
                    ·
                      refine ⟨4213174495664278632665309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44940527953752305415096629 4213174495664278632665309)
                      ·
                        rfl

theorem cell23_8205128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_8205128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205128 prefixEnd_8205128 := by exact prefixLift 8205128
  have htrace : WordTrace (prefixWord ++ tailWord_8205128) baseStart_8205128 baseEnd_8205128 := by
    simpa [prefixWord, tailWord_8205128, baseEnd_8205128] using wordTrace_append hprefix tailTrace_8205128
  have hstable : (prefixWord ++ tailWord_8205128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205128).length < 2 ^ (prefixWord ++ tailWord_8205128).sum := by decide
  have hdescent : baseEnd_8205128 < baseStart_8205128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205138 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_8205138 : Nat := 118140960795 + 8205138 * 2 ^ 59
def prefixEnd_8205138 : Nat := 4983230072969 + 3 ^ 40 * 8205138 * 2
def baseEnd_8205138 : Nat := 4213179630470823593540263

theorem tailTrace_8205138 : CollatzResearch.WordTrace tailWord_8205138 prefixEnd_8205138 4213179630470823593540263 := by
  unfold tailWord_8205138
  simp only [CollatzResearch.WordTrace]
  refine ⟨74816492137048456712562017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199510645698795884566832045 74816492137048456712562017)
  ·
    refine ⟨56112369102786342534421513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74816492137048456712562017 56112369102786342534421513)
    ·
      refine ⟨42084276827089756900816135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56112369102786342534421513 42084276827089756900816135)
      ·
        refine ⟨63126415240634635351224203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42084276827089756900816135 63126415240634635351224203)
        ·
          refine ⟨94689622860951953026836305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63126415240634635351224203 94689622860951953026836305)
          ·
            refine ⟨71017217145713964770127229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94689622860951953026836305 71017217145713964770127229)
            ·
              refine ⟨26631456429642736788797711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71017217145713964770127229 26631456429642736788797711)
              ·
                refine ⟨39947184644464105183196567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26631456429642736788797711 39947184644464105183196567)
                ·
                  refine ⟨59920776966696157774794851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39947184644464105183196567 59920776966696157774794851)
                  ·
                    refine ⟨89881165450044236662192277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59920776966696157774794851 89881165450044236662192277)
                    ·
                      refine ⟨4213179630470823593540263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89881165450044236662192277 4213179630470823593540263)
                      ·
                        rfl

theorem cell23_8205138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_8205138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205138 prefixEnd_8205138 := by exact prefixLift 8205138
  have htrace : WordTrace (prefixWord ++ tailWord_8205138) baseStart_8205138 baseEnd_8205138 := by
    simpa [prefixWord, tailWord_8205138, baseEnd_8205138] using wordTrace_append hprefix tailTrace_8205138
  have hstable : (prefixWord ++ tailWord_8205138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205138).length < 2 ^ (prefixWord ++ tailWord_8205138).sum := by decide
  have hdescent : baseEnd_8205138 < baseStart_8205138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205145 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 3]
def baseStart_8205145 : Nat := 118140960795 + 8205145 * 2 ^ 59
def prefixEnd_8205145 : Nat := 4983230072969 + 3 ^ 40 * 8205145 * 2
def baseEnd_8205145 : Nat := 4213183224835405066152731

theorem tailTrace_8205145 : CollatzResearch.WordTrace tailWord_8205145 prefixEnd_8205145 4213183224835405066152731 := by
  unfold tailWord_8205145
  simp only [CollatzResearch.WordTrace]
  refine ⟨299266223859168467045752889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199510815906112311363835259 299266223859168467045752889)
  ·
    refine ⟨224449667894376350284314667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299266223859168467045752889 224449667894376350284314667)
    ·
      refine ⟨336674501841564525426472001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224449667894376350284314667 336674501841564525426472001)
      ·
        refine ⟨252505876381173394069854001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336674501841564525426472001 252505876381173394069854001)
        ·
          refine ⟨189379407285880045552390501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252505876381173394069854001 189379407285880045552390501)
          ·
            refine ⟨35508638866102508541073219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189379407285880045552390501 35508638866102508541073219)
            ·
              refine ⟨53262958299153762811609829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35508638866102508541073219 53262958299153762811609829)
              ·
                refine ⟨9986804681091330527176843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53262958299153762811609829 9986804681091330527176843)
                ·
                  refine ⟨14980207021636995790765265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986804681091330527176843 14980207021636995790765265)
                  ·
                    refine ⟨11235155266227746843073949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14980207021636995790765265 11235155266227746843073949)
                    ·
                      refine ⟨4213183224835405066152731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11235155266227746843073949 4213183224835405066152731)
                      ·
                        rfl

theorem cell23_8205145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_8205145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205145 prefixEnd_8205145 := by exact prefixLift 8205145
  have htrace : WordTrace (prefixWord ++ tailWord_8205145) baseStart_8205145 baseEnd_8205145 := by
    simpa [prefixWord, tailWord_8205145, baseEnd_8205145] using wordTrace_append hprefix tailTrace_8205145
  have hstable : (prefixWord ++ tailWord_8205145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205145).length < 2 ^ (prefixWord ++ tailWord_8205145).sum := by decide
  have hdescent : baseEnd_8205145 < baseStart_8205145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205161 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 3, 9]
def baseStart_8205161 : Nat := 118140960795 + 8205161 * 2 ^ 59
def prefixEnd_8205161 : Nat := 4983230072969 + 3 ^ 40 * 8205161 * 2
def baseEnd_8205161 : Nat := 1404397146841959001184219

theorem tailTrace_8205161 : CollatzResearch.WordTrace tailWord_8205161 prefixEnd_8205161 1404397146841959001184219 := by
  unfold tailWord_8205161
  simp only [CollatzResearch.WordTrace]
  refine ⟨299266807427110501778335337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199511204951407001185556891 299266807427110501778335337)
  ·
    refine ⟨224450105570332876333751503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299266807427110501778335337 224450105570332876333751503)
    ·
      refine ⟨336675158355499314500627255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224450105570332876333751503 336675158355499314500627255)
      ·
        refine ⟨505012737533248971750940883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336675158355499314500627255 505012737533248971750940883)
        ·
          refine ⟨757519106299873457626411325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505012737533248971750940883 757519106299873457626411325)
          ·
            refine ⟨284069664862452546609904247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 757519106299873457626411325 284069664862452546609904247)
            ·
              refine ⟨426104497293678819914856371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284069664862452546609904247 426104497293678819914856371)
              ·
                refine ⟨639156745940518229872284557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426104497293678819914856371 639156745940518229872284557)
                ·
                  refine ⟨239683779727694336202106709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639156745940518229872284557 239683779727694336202106709)
                  ·
                    refine ⟨1404397146841959001184219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 239683779727694336202106709 1404397146841959001184219)
                    ·
                      rfl

theorem cell23_8205161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_8205161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205161 prefixEnd_8205161 := by exact prefixLift 8205161
  have htrace : WordTrace (prefixWord ++ tailWord_8205161) baseStart_8205161 baseEnd_8205161 := by
    simpa [prefixWord, tailWord_8205161, baseEnd_8205161] using wordTrace_append hprefix tailTrace_8205161
  have hstable : (prefixWord ++ tailWord_8205161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205161).length < 2 ^ (prefixWord ++ tailWord_8205161).sum := by decide
  have hdescent : baseEnd_8205161 < baseStart_8205161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205182 : List Nat := [4, 2, 3, 1, 2, 1, 2, 8]
def baseStart_8205182 : Nat := 118140960795 + 8205182 * 2 ^ 59
def prefixEnd_8205182 : Nat := 4983230072969 + 3 ^ 40 * 8205182 * 2
def baseEnd_8205182 : Nat := 156044526800726719310743

theorem tailTrace_8205182 : CollatzResearch.WordTrace tailWord_8205182 prefixEnd_8205182 156044526800726719310743 := by
  unfold tailWord_8205182
  simp only [CollatzResearch.WordTrace]
  refine ⟨37408446670004302795606225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199511715573356281576566533 37408446670004302795606225)
  ·
    refine ⟨28056335002503227096704669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37408446670004302795606225 28056335002503227096704669)
    ·
      refine ⟨10521125625938710161264251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28056335002503227096704669 10521125625938710161264251)
      ·
        refine ⟨15781688438908065241896377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10521125625938710161264251 15781688438908065241896377)
        ·
          refine ⟨11836266329181048931422283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15781688438908065241896377 11836266329181048931422283)
          ·
            refine ⟨17754399493771573397133425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11836266329181048931422283 17754399493771573397133425)
            ·
              refine ⟨13315799620328680047850069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17754399493771573397133425 13315799620328680047850069)
              ·
                refine ⟨156044526800726719310743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13315799620328680047850069 156044526800726719310743)
                ·
                  rfl

theorem cell23_8205182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_8205182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205182 prefixEnd_8205182 := by exact prefixLift 8205182
  have htrace : WordTrace (prefixWord ++ tailWord_8205182) baseStart_8205182 baseEnd_8205182 := by
    simpa [prefixWord, tailWord_8205182, baseEnd_8205182] using wordTrace_append hprefix tailTrace_8205182
  have hstable : (prefixWord ++ tailWord_8205182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205182).length < 2 ^ (prefixWord ++ tailWord_8205182).sum := by decide
  have hdescent : baseEnd_8205182 < baseStart_8205182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205186 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_8205186 : Nat := 118140960795 + 8205186 * 2 ^ 59
def prefixEnd_8205186 : Nat := 4983230072969 + 3 ^ 40 * 8205186 * 2
def baseEnd_8205186 : Nat := 1404401425847413135246681

theorem tailTrace_8205186 : CollatzResearch.WordTrace tailWord_8205186 prefixEnd_8205186 1404401425847413135246681 := by
  unfold tailWord_8205186
  simp only [CollatzResearch.WordTrace]
  refine ⟨74816929813004982761998853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199511812834679954031996941 74816929813004982761998853)
  ·
    refine ⟨14028174339938434267874785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74816929813004982761998853 14028174339938434267874785)
    ·
      refine ⟨10521130754953825700906089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14028174339938434267874785 10521130754953825700906089)
      ·
        refine ⟨7890848066215369275679567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10521130754953825700906089 7890848066215369275679567)
        ·
          refine ⟨11836272099323053913519351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7890848066215369275679567 11836272099323053913519351)
          ·
            refine ⟨17754408148984580870279027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11836272099323053913519351 17754408148984580870279027)
            ·
              refine ⟨26631612223476871305418541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17754408148984580870279027 26631612223476871305418541)
              ·
                refine ⟨9986854583803826739531953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26631612223476871305418541 9986854583803826739531953)
                ·
                  refine ⟨7490140937852870054648965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986854583803826739531953 7490140937852870054648965)
                  ·
                    refine ⟨1404401425847413135246681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7490140937852870054648965 1404401425847413135246681)
                    ·
                      rfl

theorem cell23_8205186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_8205186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205186 prefixEnd_8205186 := by exact prefixLift 8205186
  have htrace : WordTrace (prefixWord ++ tailWord_8205186) baseStart_8205186 baseEnd_8205186 := by
    simpa [prefixWord, tailWord_8205186, baseEnd_8205186] using wordTrace_append hprefix tailTrace_8205186
  have hstable : (prefixWord ++ tailWord_8205186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205186).length < 2 ^ (prefixWord ++ tailWord_8205186).sum := by decide
  have hdescent : baseEnd_8205186 < baseStart_8205186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205228 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_8205228 : Nat := 118140960795 + 8205228 * 2 ^ 59
def prefixEnd_8205228 : Nat := 4983230072969 + 3 ^ 40 * 8205228 * 2
def baseEnd_8205228 : Nat := 4213225843729728241414849

theorem tailTrace_8205228 : CollatzResearch.WordTrace tailWord_8205228 prefixEnd_8205228 4213225843729728241414849 := by
  unfold tailWord_8205228
  simp only [CollatzResearch.WordTrace]
  refine ⟨149634625558933886110512169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199512834078578514814016225 149634625558933886110512169)
  ·
    refine ⟨112225969169200414582884127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149634625558933886110512169 112225969169200414582884127)
    ·
      refine ⟨168338953753800621874326191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112225969169200414582884127 168338953753800621874326191)
      ·
        refine ⟨252508430630700932811489287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168338953753800621874326191 252508430630700932811489287)
        ·
          refine ⟨378762645946051399217233931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252508430630700932811489287 378762645946051399217233931)
          ·
            refine ⟨568143968919077098825850897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378762645946051399217233931 568143968919077098825850897)
            ·
              refine ⟨426107976689307824119388173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568143968919077098825850897 426107976689307824119388173)
              ·
                refine ⟨159790491258490434044770565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426107976689307824119388173 159790491258490434044770565)
                ·
                  refine ⟨29960717110966956383394481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159790491258490434044770565 29960717110966956383394481)
                  ·
                    refine ⟨22470537833225217287545861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29960717110966956383394481 22470537833225217287545861)
                    ·
                      refine ⟨4213225843729728241414849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22470537833225217287545861 4213225843729728241414849)
                      ·
                        rfl

theorem cell23_8205228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_8205228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205228 prefixEnd_8205228 := by exact prefixLift 8205228
  have htrace : WordTrace (prefixWord ++ tailWord_8205228) baseStart_8205228 baseEnd_8205228 := by
    simpa [prefixWord, tailWord_8205228, baseEnd_8205228] using wordTrace_append hprefix tailTrace_8205228
  have hstable : (prefixWord ++ tailWord_8205228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205228).length < 2 ^ (prefixWord ++ tailWord_8205228).sum := by decide
  have hdescent : baseEnd_8205228 < baseStart_8205228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205272 : List Nat := [2, 1, 2, 2, 2, 4, 2, 3, 5]
def baseStart_8205272 : Nat := 118140960795 + 8205272 * 2 ^ 59
def prefixEnd_8205272 : Nat := 4983230072969 + 3 ^ 40 * 8205272 * 2
def baseEnd_8205272 : Nat := 468138715208725118807183

theorem tailTrace_8205272 : CollatzResearch.WordTrace tailWord_8205272 prefixEnd_8205272 468138715208725118807183 := by
  unfold tailWord_8205272
  simp only [CollatzResearch.WordTrace]
  refine ⟨149635427964854183867813035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199513903953138911823750713 149635427964854183867813035)
  ·
    refine ⟨224453141947281275801719553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149635427964854183867813035 224453141947281275801719553)
    ·
      refine ⟨168339856460460956851289665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224453141947281275801719553 168339856460460956851289665)
      ·
        refine ⟨126254892345345717638467249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168339856460460956851289665 126254892345345717638467249)
        ·
          refine ⟨94691169259009288228850437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126254892345345717638467249 94691169259009288228850437)
          ·
            refine ⟨17754594236064241542909457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94691169259009288228850437 17754594236064241542909457)
            ·
              refine ⟨13315945677048181157182093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17754594236064241542909457 13315945677048181157182093)
              ·
                refine ⟨4993479628893067933943285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13315945677048181157182093 4993479628893067933943285)
                ·
                  refine ⟨468138715208725118807183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4993479628893067933943285 468138715208725118807183)
                  ·
                    rfl

theorem cell23_8205272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 5].length) (baseStart_8205272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205272 prefixEnd_8205272 := by exact prefixLift 8205272
  have htrace : WordTrace (prefixWord ++ tailWord_8205272) baseStart_8205272 baseEnd_8205272 := by
    simpa [prefixWord, tailWord_8205272, baseEnd_8205272] using wordTrace_append hprefix tailTrace_8205272
  have hstable : (prefixWord ++ tailWord_8205272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205272).length < 2 ^ (prefixWord ++ tailWord_8205272).sum := by decide
  have hdescent : baseEnd_8205272 < baseStart_8205272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205345 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 8]
def baseStart_8205345 : Nat := 118140960795 + 8205345 * 2 ^ 59
def prefixEnd_8205345 : Nat := 4983230072969 + 3 ^ 40 * 8205345 * 2
def baseEnd_8205345 : Nat := 468142880107367142627979

theorem tailTrace_8205345 : CollatzResearch.WordTrace tailWord_8205345 prefixEnd_8205345 468142880107367142627979 := by
  unfold tailWord_8205345
  simp only [CollatzResearch.WordTrace]
  refine ⟨299273518458443901203033489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199515678972295934135355659 299273518458443901203033489)
  ·
    refine ⟨224455138843832925902275117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299273518458443901203033489 224455138843832925902275117)
    ·
      refine ⟨84170677066437347213353169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224455138843832925902275117 84170677066437347213353169)
      ·
        refine ⟨63128007799828010410014877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84170677066437347213353169 63128007799828010410014877)
        ·
          refine ⟨23673002924935503903755579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63128007799828010410014877 23673002924935503903755579)
          ·
            refine ⟨35509504387403255855633369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23673002924935503903755579 35509504387403255855633369)
            ·
              refine ⟨26632128290552441891725027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35509504387403255855633369 26632128290552441891725027)
              ·
                refine ⟨39948192435828662837587541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26632128290552441891725027 39948192435828662837587541)
                ·
                  refine ⟨468142880107367142627979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39948192435828662837587541 468142880107367142627979)
                  ·
                    rfl

theorem cell23_8205345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 8].length) (baseStart_8205345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205345 prefixEnd_8205345 := by exact prefixLift 8205345
  have htrace : WordTrace (prefixWord ++ tailWord_8205345) baseStart_8205345 baseEnd_8205345 := by
    simpa [prefixWord, tailWord_8205345, baseEnd_8205345] using wordTrace_append hprefix tailTrace_8205345
  have hstable : (prefixWord ++ tailWord_8205345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205345).length < 2 ^ (prefixWord ++ tailWord_8205345).sum := by decide
  have hdescent : baseEnd_8205345 < baseStart_8205345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205395 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 4]
def baseStart_8205395 : Nat := 118140960795 + 8205395 * 2 ^ 59
def prefixEnd_8205395 : Nat := 4983230072969 + 3 ^ 40 * 8205395 * 2
def baseEnd_8205395 : Nat := 4213311594999029088026581

theorem tailTrace_8205395 : CollatzResearch.WordTrace tailWord_8205395 prefixEnd_8205395 4213311594999029088026581 := by
  unfold tailWord_8205395
  simp only [CollatzResearch.WordTrace]
  refine ⟨299275342108262759742353639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199516894738841839828235759 299275342108262759742353639)
  ·
    refine ⟨448913013162394139613530459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299275342108262759742353639 448913013162394139613530459)
    ·
      refine ⟨673369519743591209420295689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448913013162394139613530459 673369519743591209420295689)
      ·
        refine ⟨505027139807693407065221767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673369519743591209420295689 505027139807693407065221767)
        ·
          refine ⟨757540709711540110597832651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505027139807693407065221767 757540709711540110597832651)
          ·
            refine ⟨1136311064567310165896748977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757540709711540110597832651 1136311064567310165896748977)
            ·
              refine ⟨852233298425482624422561733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1136311064567310165896748977 852233298425482624422561733)
              ·
                refine ⟨159793743454777992079230325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 852233298425482624422561733 159793743454777992079230325)
                ·
                  refine ⟨14980663448885436757427843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159793743454777992079230325 14980663448885436757427843)
                  ·
                    refine ⟨22470995173328155136141765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14980663448885436757427843 22470995173328155136141765)
                    ·
                      refine ⟨4213311594999029088026581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22470995173328155136141765 4213311594999029088026581)
                      ·
                        rfl

theorem cell23_8205395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_8205395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205395 prefixEnd_8205395 := by exact prefixLift 8205395
  have htrace : WordTrace (prefixWord ++ tailWord_8205395) baseStart_8205395 baseEnd_8205395 := by
    simpa [prefixWord, tailWord_8205395, baseEnd_8205395] using wordTrace_append hprefix tailTrace_8205395
  have hstable : (prefixWord ++ tailWord_8205395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205395).length < 2 ^ (prefixWord ++ tailWord_8205395).sum := by decide
  have hdescent : baseEnd_8205395 < baseStart_8205395 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205412 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_8205412 : Nat := 118140960795 + 8205412 * 2 ^ 59
def prefixEnd_8205412 : Nat := 4983230072969 + 3 ^ 40 * 8205412 * 2
def baseEnd_8205412 : Nat := 4213320324170155521514003

theorem tailTrace_8205412 : CollatzResearch.WordTrace tailWord_8205412 prefixEnd_8205412 4213320324170155521514003 := by
  unfold tailWord_8205412
  simp only [CollatzResearch.WordTrace]
  refine ⟨149637981074600585822861245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199517308099467447763814993 149637981074600585822861245)
  ·
    refine ⟨56114242902975219683572967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149637981074600585822861245 56114242902975219683572967)
    ·
      refine ⟨84171364354462829525359451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56114242902975219683572967 84171364354462829525359451)
      ·
        refine ⟨126257046531694244288039177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84171364354462829525359451 126257046531694244288039177)
        ·
          refine ⟨94692784898770683216029383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126257046531694244288039177 94692784898770683216029383)
          ·
            refine ⟨142039177348156024824044075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94692784898770683216029383 142039177348156024824044075)
            ·
              refine ⟨213058766022234037236066113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142039177348156024824044075 213058766022234037236066113)
              ·
                refine ⟨159794074516675527927049585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213058766022234037236066113 159794074516675527927049585)
                ·
                  refine ⟨119845555887506645945287189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159794074516675527927049585 119845555887506645945287189)
                  ·
                    refine ⟨5617760432226874028685337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119845555887506645945287189 5617760432226874028685337)
                    ·
                      refine ⟨4213320324170155521514003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617760432226874028685337 4213320324170155521514003)
                      ·
                        rfl

theorem cell23_8205412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_8205412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205412 prefixEnd_8205412 := by exact prefixLift 8205412
  have htrace : WordTrace (prefixWord ++ tailWord_8205412) baseStart_8205412 baseEnd_8205412 := by
    simpa [prefixWord, tailWord_8205412, baseEnd_8205412] using wordTrace_append hprefix tailTrace_8205412
  have hstable : (prefixWord ++ tailWord_8205412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205412).length < 2 ^ (prefixWord ++ tailWord_8205412).sum := by decide
  have hdescent : baseEnd_8205412 < baseStart_8205412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205422 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_8205422 : Nat := 118140960795 + 8205422 * 2 ^ 59
def prefixEnd_8205422 : Nat := 4983230072969 + 3 ^ 40 * 8205422 * 2
def baseEnd_8205422 : Nat := 1404441819658900160796319

theorem tailTrace_8205422 : CollatzResearch.WordTrace tailWord_8205422 prefixEnd_8205422 1404441819658900160796319 := by
  unfold tailWord_8205422
  simp only [CollatzResearch.WordTrace]
  refine ⟨37409540859895617919198315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199517551252776628902391013 37409540859895617919198315)
  ·
    refine ⟨56114311289843426878797473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37409540859895617919198315 56114311289843426878797473)
    ·
      refine ⟨42085733467382570159098105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56114311289843426878797473 42085733467382570159098105)
      ·
        refine ⟨31564300100536927619323579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42085733467382570159098105 31564300100536927619323579)
        ·
          refine ⟨47346450150805391428985369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31564300100536927619323579 47346450150805391428985369)
          ·
            refine ⟨35509837613104043571739027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47346450150805391428985369 35509837613104043571739027)
            ·
              refine ⟨53264756419656065357608541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35509837613104043571739027 53264756419656065357608541)
              ·
                refine ⟨19974283657371024509103203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53264756419656065357608541 19974283657371024509103203)
                ·
                  refine ⟨29961425486056536763654805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19974283657371024509103203 29961425486056536763654805)
                  ·
                    refine ⟨1404441819658900160796319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29961425486056536763654805 1404441819658900160796319)
                    ·
                      rfl

theorem cell23_8205422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_8205422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205422 prefixEnd_8205422 := by exact prefixLift 8205422
  have htrace : WordTrace (prefixWord ++ tailWord_8205422) baseStart_8205422 baseEnd_8205422 := by
    simpa [prefixWord, tailWord_8205422, baseEnd_8205422] using wordTrace_append hprefix tailTrace_8205422
  have hstable : (prefixWord ++ tailWord_8205422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205422).length < 2 ^ (prefixWord ++ tailWord_8205422).sum := by decide
  have hdescent : baseEnd_8205422 < baseStart_8205422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205432 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_8205432 : Nat := 118140960795 + 8205432 * 2 ^ 59
def prefixEnd_8205432 : Nat := 4983230072969 + 3 ^ 40 * 8205432 * 2
def baseEnd_8205432 : Nat := 4213330593783245443263911

theorem tailTrace_8205432 : CollatzResearch.WordTrace tailWord_8205432 prefixEnd_8205432 4213330593783245443263911 := by
  unfold tailWord_8205432
  simp only [CollatzResearch.WordTrace]
  refine ⟨149638345804564357530725275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199517794406085810040967033 149638345804564357530725275)
  ·
    refine ⟨224457518706846536296087913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149638345804564357530725275 224457518706846536296087913)
    ·
      refine ⟨168343139030134902222065935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224457518706846536296087913 168343139030134902222065935)
      ·
        refine ⟨252514708545202353333098903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168343139030134902222065935 252514708545202353333098903)
        ·
          refine ⟨378772062817803529999648355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252514708545202353333098903 378772062817803529999648355)
          ·
            refine ⟨568158094226705294999472533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378772062817803529999648355 568158094226705294999472533)
            ·
              refine ⟨26632410666876810703100275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 568158094226705294999472533 26632410666876810703100275)
              ·
                refine ⟨39948616000315216054650413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26632410666876810703100275 39948616000315216054650413)
                ·
                  refine ⟨14980731000118206020493905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39948616000315216054650413 14980731000118206020493905)
                  ·
                    refine ⟨11235548250088654515370429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14980731000118206020493905 11235548250088654515370429)
                    ·
                      refine ⟨4213330593783245443263911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11235548250088654515370429 4213330593783245443263911)
                      ·
                        rfl

theorem cell23_8205432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_8205432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205432 prefixEnd_8205432 := by exact prefixLift 8205432
  have htrace : WordTrace (prefixWord ++ tailWord_8205432) baseStart_8205432 baseEnd_8205432 := by
    simpa [prefixWord, tailWord_8205432, baseEnd_8205432] using wordTrace_append hprefix tailTrace_8205432
  have hstable : (prefixWord ++ tailWord_8205432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205432).length < 2 ^ (prefixWord ++ tailWord_8205432).sum := by decide
  have hdescent : baseEnd_8205432 < baseStart_8205432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205433 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 2, 3, 2]
def baseStart_8205433 : Nat := 118140960795 + 8205433 * 2 ^ 59
def prefixEnd_8205433 : Nat := 4983230072969 + 3 ^ 40 * 8205433 * 2
def baseEnd_8205433 : Nat := 4213331107263899939351407

theorem tailTrace_8205433 : CollatzResearch.WordTrace tailWord_8205433 prefixEnd_8205433 4213331107263899939351407 := by
  unfold tailWord_8205433
  simp only [CollatzResearch.WordTrace]
  refine ⟨299276728082125092232236953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199517818721416728154824635 299276728082125092232236953)
  ·
    refine ⟨224457546061593819174177715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299276728082125092232236953 224457546061593819174177715)
    ·
      refine ⟨336686319092390728761266573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224457546061593819174177715 336686319092390728761266573)
      ·
        refine ⟨126257369659646523285474965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336686319092390728761266573 126257369659646523285474965)
        ·
          refine ⟨5918314202795930779006639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126257369659646523285474965 5918314202795930779006639)
          ·
            refine ⟨8877471304193896168509959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918314202795930779006639 8877471304193896168509959)
            ·
              refine ⟨13316206956290844252764939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8877471304193896168509959 13316206956290844252764939)
              ·
                refine ⟨19974310434436266379147409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13316206956290844252764939 19974310434436266379147409)
                ·
                  refine ⟨14980732825827199784360557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19974310434436266379147409 14980732825827199784360557)
                  ·
                    refine ⟨5617774809685199919135209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14980732825827199784360557 5617774809685199919135209)
                    ·
                      refine ⟨4213331107263899939351407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617774809685199919135209 4213331107263899939351407)
                      ·
                        rfl

theorem cell23_8205433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_8205433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205433 prefixEnd_8205433 := by exact prefixLift 8205433
  have htrace : WordTrace (prefixWord ++ tailWord_8205433) baseStart_8205433 baseEnd_8205433 := by
    simpa [prefixWord, tailWord_8205433, baseEnd_8205433] using wordTrace_append hprefix tailTrace_8205433
  have hstable : (prefixWord ++ tailWord_8205433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205433).length < 2 ^ (prefixWord ++ tailWord_8205433).sum := by decide
  have hdescent : baseEnd_8205433 < baseStart_8205433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205449 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 3]
def baseStart_8205449 : Nat := 118140960795 + 8205449 * 2 ^ 59
def prefixEnd_8205449 : Nat := 4983230072969 + 3 ^ 40 * 8205449 * 2
def baseEnd_8205449 : Nat := 4213339322954371876751333

theorem tailTrace_8205449 : CollatzResearch.WordTrace tailWord_8205449 prefixEnd_8205449 4213339322954371876751333 := by
  unfold tailWord_8205449
  simp only [CollatzResearch.WordTrace]
  refine ⟨299277311650067126964819401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199518207766711417976546267 299277311650067126964819401)
  ·
    refine ⟨224457983737550345223614551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299277311650067126964819401 224457983737550345223614551)
    ·
      refine ⟨336686975606325517835421827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224457983737550345223614551 336686975606325517835421827)
      ·
        refine ⟨505030463409488276753132741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336686975606325517835421827 505030463409488276753132741)
        ·
          refine ⟨94693211889279051891212389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505030463409488276753132741 94693211889279051891212389)
          ·
            refine ⟨17754977229239822229602323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94693211889279051891212389 17754977229239822229602323)
            ·
              refine ⟨26632465843859733344403485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17754977229239822229602323 26632465843859733344403485)
              ·
                refine ⟨9987174691447400004151307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26632465843859733344403485 9987174691447400004151307)
                ·
                  refine ⟨14980762037171100006226961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9987174691447400004151307 14980762037171100006226961)
                  ·
                    refine ⟨11235571527878325004670221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14980762037171100006226961 11235571527878325004670221)
                    ·
                      refine ⟨4213339322954371876751333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11235571527878325004670221 4213339322954371876751333)
                      ·
                        rfl

theorem cell23_8205449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 3].length) (baseStart_8205449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205449 prefixEnd_8205449 := by exact prefixLift 8205449
  have htrace : WordTrace (prefixWord ++ tailWord_8205449) baseStart_8205449 baseEnd_8205449 := by
    simpa [prefixWord, tailWord_8205449, baseEnd_8205449] using wordTrace_append hprefix tailTrace_8205449
  have hstable : (prefixWord ++ tailWord_8205449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205449).length < 2 ^ (prefixWord ++ tailWord_8205449).sum := by decide
  have hdescent : baseEnd_8205449 < baseStart_8205449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205463 : List Nat := [1, 1, 3, 3, 3, 1, 2, 4, 1, 2, 2]
def baseStart_8205463 : Nat := 118140960795 + 8205463 * 2 ^ 59
def prefixEnd_8205463 : Nat := 4983230072969 + 3 ^ 40 * 8205463 * 2
def baseEnd_8205463 : Nat := 4213346511683534821976269

theorem tailTrace_8205463 : CollatzResearch.WordTrace tailWord_8205463 prefixEnd_8205463 4213346511683534821976269 := by
  unfold tailWord_8205463
  simp only [CollatzResearch.WordTrace]
  refine ⟨299277822272016407355829043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199518548181344271570552695 299277822272016407355829043)
  ·
    refine ⟨448916733408024611033743565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299277822272016407355829043 448916733408024611033743565)
    ·
      refine ⟨168343775028009229137653837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448916733408024611033743565 168343775028009229137653837)
      ·
        refine ⟨63128915635503460926620189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168343775028009229137653837 63128915635503460926620189)
        ·
          refine ⟨23673343363313797847482571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63128915635503460926620189 23673343363313797847482571)
          ·
            refine ⟨35510015044970696771223857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23673343363313797847482571 35510015044970696771223857)
            ·
              refine ⟨26632511283728022578417893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35510015044970696771223857 26632511283728022578417893)
              ·
                refine ⟨4993595865699004233453355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26632511283728022578417893 4993595865699004233453355)
                ·
                  refine ⟨7490393798548506350180033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993595865699004233453355 7490393798548506350180033)
                  ·
                    refine ⟨5617795348911379762635025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7490393798548506350180033 5617795348911379762635025)
                    ·
                      refine ⟨4213346511683534821976269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617795348911379762635025 4213346511683534821976269)
                      ·
                        rfl

theorem cell23_8205463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_8205463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205463 prefixEnd_8205463 := by exact prefixLift 8205463
  have htrace : WordTrace (prefixWord ++ tailWord_8205463) baseStart_8205463 baseEnd_8205463 := by
    simpa [prefixWord, tailWord_8205463, baseEnd_8205463] using wordTrace_append hprefix tailTrace_8205463
  have hstable : (prefixWord ++ tailWord_8205463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205463).length < 2 ^ (prefixWord ++ tailWord_8205463).sum := by decide
  have hdescent : baseEnd_8205463 < baseStart_8205463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205475 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 5]
def baseStart_8205475 : Nat := 118140960795 + 8205475 * 2 ^ 59
def prefixEnd_8205475 : Nat := 4983230072969 + 3 ^ 40 * 8205475 * 2
def baseEnd_8205475 : Nat := 4213352673451388775026213

theorem tailTrace_8205475 : CollatzResearch.WordTrace tailWord_8205475 prefixEnd_8205475 4213352673451388775026213 := by
  unfold tailWord_8205475
  simp only [CollatzResearch.WordTrace]
  refine ⟨299278259947972933405265879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199518839965315288936843919 299278259947972933405265879)
  ·
    refine ⟨448917389921959400107898819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299278259947972933405265879 448917389921959400107898819)
    ·
      refine ⟨673376084882939100161848229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448917389921959400107898819 673376084882939100161848229)
      ·
        refine ⟨126258015915551081280346543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 673376084882939100161848229 126258015915551081280346543)
        ·
          refine ⟨189387023873326621920519815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126258015915551081280346543 189387023873326621920519815)
          ·
            refine ⟨284080535809989932880779723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189387023873326621920519815 284080535809989932880779723)
            ·
              refine ⟨426120803714984899321169585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284080535809989932880779723 426120803714984899321169585)
              ·
                refine ⟨319590602786238674490877189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426120803714984899321169585 319590602786238674490877189)
                ·
                  refine ⟨59923238022419751467039473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319590602786238674490877189 59923238022419751467039473)
                  ·
                    refine ⟨44942428516814813600279605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59923238022419751467039473 44942428516814813600279605)
                    ·
                      refine ⟨4213352673451388775026213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44942428516814813600279605 4213352673451388775026213)
                      ·
                        rfl

theorem cell23_8205475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_8205475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205475 prefixEnd_8205475 := by exact prefixLift 8205475
  have htrace : WordTrace (prefixWord ++ tailWord_8205475) baseStart_8205475 baseEnd_8205475 := by
    simpa [prefixWord, tailWord_8205475, baseEnd_8205475] using wordTrace_append hprefix tailTrace_8205475
  have hstable : (prefixWord ++ tailWord_8205475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205475).length < 2 ^ (prefixWord ++ tailWord_8205475).sum := by decide
  have hdescent : baseEnd_8205475 < baseStart_8205475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205515 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 6]
def baseStart_8205515 : Nat := 118140960795 + 8205515 * 2 ^ 59
def prefixEnd_8205515 : Nat := 4983230072969 + 3 ^ 40 * 8205515 * 2
def baseEnd_8205515 : Nat := 4213373212677568618526029

theorem tailTrace_8205515 : CollatzResearch.WordTrace tailWord_8205515 prefixEnd_8205515 4213373212677568618526029 := by
  unfold tailWord_8205515
  simp only [CollatzResearch.WordTrace]
  refine ⟨299279718867828020236721999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199519812578552013491147999 299279718867828020236721999)
  ·
    refine ⟨448919578301742030355082999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299279718867828020236721999 448919578301742030355082999)
    ·
      refine ⟨673379367452613045532624499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448919578301742030355082999 673379367452613045532624499)
      ·
        refine ⟨1010069051178919568298936749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673379367452613045532624499 1010069051178919568298936749)
        ·
          refine ⟨378775894192094838112101281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1010069051178919568298936749 378775894192094838112101281)
          ·
            refine ⟨284081920644071128584075961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378775894192094838112101281 284081920644071128584075961)
            ·
              refine ⟨213061440483053346438056971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284081920644071128584075961 213061440483053346438056971)
              ·
                refine ⟨319592160724580019657085457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213061440483053346438056971 319592160724580019657085457)
                ·
                  refine ⟨239694120543435014742814093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319592160724580019657085457 239694120543435014742814093)
                  ·
                    refine ⟨89885295203788130528555285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239694120543435014742814093 89885295203788130528555285)
                    ·
                      refine ⟨4213373212677568618526029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89885295203788130528555285 4213373212677568618526029)
                      ·
                        rfl

theorem cell23_8205515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_8205515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205515 prefixEnd_8205515 := by exact prefixLift 8205515
  have htrace : WordTrace (prefixWord ++ tailWord_8205515) baseStart_8205515 baseEnd_8205515 := by
    simpa [prefixWord, tailWord_8205515, baseEnd_8205515] using wordTrace_append hprefix tailTrace_8205515
  have hstable : (prefixWord ++ tailWord_8205515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205515).length < 2 ^ (prefixWord ++ tailWord_8205515).sum := by decide
  have hdescent : baseEnd_8205515 < baseStart_8205515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205522 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_8205522 : Nat := 118140960795 + 8205522 * 2 ^ 59
def prefixEnd_8205522 : Nat := 4983230072969 + 3 ^ 40 * 8205522 * 2
def baseEnd_8205522 : Nat := 4213376807042150091138497

theorem tailTrace_8205522 : CollatzResearch.WordTrace tailWord_8205522 prefixEnd_8205522 4213376807042150091138497 := by
  unfold tailWord_8205522
  simp only [CollatzResearch.WordTrace]
  refine ⟨74819993544700665108056705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199519982785868440288151213 74819993544700665108056705)
  ·
    refine ⟨56114995158525498831042529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74819993544700665108056705 56114995158525498831042529)
    ·
      refine ⟨42086246368894124123281897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56114995158525498831042529 42086246368894124123281897)
      ·
        refine ⟨31564684776670593092461423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42086246368894124123281897 31564684776670593092461423)
        ·
          refine ⟨47347027165005889638692135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31564684776670593092461423 47347027165005889638692135)
          ·
            refine ⟨71020540747508834458038203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47347027165005889638692135 71020540747508834458038203)
            ·
              refine ⟨106530811121263251687057305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71020540747508834458038203 106530811121263251687057305)
              ·
                refine ⟨79898108340947438765292979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106530811121263251687057305 79898108340947438765292979)
                ·
                  refine ⟨119847162511421158147939469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79898108340947438765292979 119847162511421158147939469)
                  ·
                    refine ⟨44942685941782934305477301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119847162511421158147939469 44942685941782934305477301)
                    ·
                      refine ⟨4213376807042150091138497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44942685941782934305477301 4213376807042150091138497)
                      ·
                        rfl

theorem cell23_8205522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_8205522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205522 prefixEnd_8205522 := by exact prefixLift 8205522
  have htrace : WordTrace (prefixWord ++ tailWord_8205522) baseStart_8205522 baseEnd_8205522 := by
    simpa [prefixWord, tailWord_8205522, baseEnd_8205522] using wordTrace_append hprefix tailTrace_8205522
  have hstable : (prefixWord ++ tailWord_8205522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205522).length < 2 ^ (prefixWord ++ tailWord_8205522).sum := by decide
  have hdescent : baseEnd_8205522 < baseStart_8205522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205552 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 3]
def baseStart_8205552 : Nat := 118140960795 + 8205552 * 2 ^ 59
def prefixEnd_8205552 : Nat := 4983230072969 + 3 ^ 40 * 8205552 * 2
def baseEnd_8205552 : Nat := 4213392211461784973763359

theorem tailTrace_8205552 : CollatzResearch.WordTrace tailWord_8205552 prefixEnd_8205552 4213392211461784973763359 := by
  unfold tailWord_8205552
  simp only [CollatzResearch.WordTrace]
  refine ⟨149640534184346987777909455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199520712245795983703879273 149640534184346987777909455)
  ·
    refine ⟨224460801276520481666864183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149640534184346987777909455 224460801276520481666864183)
    ·
      refine ⟨336691201914780722500296275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224460801276520481666864183 336691201914780722500296275)
      ·
        refine ⟨505036802872171083750444413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336691201914780722500296275 505036802872171083750444413)
        ·
          refine ⟨189388801077064156406416655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505036802872171083750444413 189388801077064156406416655)
          ·
            refine ⟨284083201615596234609624983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189388801077064156406416655 284083201615596234609624983)
            ·
              refine ⟨426124802423394351914437475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284083201615596234609624983 426124802423394351914437475)
              ·
                refine ⟨639187203635091527871656213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426124802423394351914437475 639187203635091527871656213)
                ·
                  refine ⟨29961900170394915368983885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639187203635091527871656213 29961900170394915368983885)
                  ·
                    refine ⟨11235712563898093263368957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29961900170394915368983885 11235712563898093263368957)
                    ·
                      refine ⟨4213392211461784973763359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11235712563898093263368957 4213392211461784973763359)
                      ·
                        rfl

theorem cell23_8205552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_8205552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205552 prefixEnd_8205552 := by exact prefixLift 8205552
  have htrace : WordTrace (prefixWord ++ tailWord_8205552) baseStart_8205552 baseEnd_8205552 := by
    simpa [prefixWord, tailWord_8205552, baseEnd_8205552] using wordTrace_append hprefix tailTrace_8205552
  have hstable : (prefixWord ++ tailWord_8205552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205552).length < 2 ^ (prefixWord ++ tailWord_8205552).sum := by decide
  have hdescent : baseEnd_8205552 < baseStart_8205552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205576 : List Nat := [2, 1, 3, 2, 4, 1, 1, 4, 5]
def baseStart_8205576 : Nat := 118140960795 + 8205576 * 2 ^ 59
def prefixEnd_8205576 : Nat := 4983230072969 + 3 ^ 40 * 8205576 * 2
def baseEnd_8205576 : Nat := 468156059444165875540361

theorem tailTrace_8205576 : CollatzResearch.WordTrace tailWord_8205576 prefixEnd_8205576 468156059444165875540361 := by
  unfold tailWord_8205576
  simp only [CollatzResearch.WordTrace]
  refine ⟨149640971860303513827346291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199521295813738018436461721 149640971860303513827346291)
  ·
    refine ⟨224461457790455270741019437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149640971860303513827346291 224461457790455270741019437)
    ·
      refine ⟨84173046671420726527882289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224461457790455270741019437 84173046671420726527882289)
      ·
        refine ⟨63129785003565544895911717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84173046671420726527882289 63129785003565544895911717)
        ·
          refine ⟨11836834688168539667983447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63129785003565544895911717 11836834688168539667983447)
          ·
            refine ⟨17755252032252809501975171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11836834688168539667983447 17755252032252809501975171)
            ·
              refine ⟨26632878048379214252962757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17755252032252809501975171 26632878048379214252962757)
              ·
                refine ⟨4993664634071102672430517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26632878048379214252962757 4993664634071102672430517)
                ·
                  refine ⟨468156059444165875540361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4993664634071102672430517 468156059444165875540361)
                  ·
                    rfl

theorem cell23_8205576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 5].length) (baseStart_8205576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205576 prefixEnd_8205576 := by exact prefixLift 8205576
  have htrace : WordTrace (prefixWord ++ tailWord_8205576) baseStart_8205576 baseEnd_8205576 := by
    simpa [prefixWord, tailWord_8205576, baseEnd_8205576] using wordTrace_append hprefix tailTrace_8205576
  have hstable : (prefixWord ++ tailWord_8205576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205576).length < 2 ^ (prefixWord ++ tailWord_8205576).sum := by decide
  have hdescent : baseEnd_8205576 < baseStart_8205576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205579 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 2, 5, 2]
def baseStart_8205579 : Nat := 118140960795 + 8205579 * 2 ^ 59
def prefixEnd_8205579 : Nat := 4983230072969 + 3 ^ 40 * 8205579 * 2
def baseEnd_8205579 : Nat := 4213406075439456368125735

theorem tailTrace_8205579 : CollatzResearch.WordTrace tailWord_8205579 prefixEnd_8205579 4213406075439456368125735 := by
  unfold tailWord_8205579
  simp only [CollatzResearch.WordTrace]
  refine ⟨299282053139596159167051791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199521368759730772778034527 299282053139596159167051791)
  ·
    refine ⟨448923079709394238750577687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299282053139596159167051791 448923079709394238750577687)
    ·
      refine ⟨673384619564091358125866531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448923079709394238750577687 673384619564091358125866531)
      ·
        refine ⟨1010076929346137037188799797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673384619564091358125866531 1010076929346137037188799797)
        ·
          refine ⟨94694712126200347236449981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1010076929346137037188799797 94694712126200347236449981)
          ·
            refine ⟨35510517047325130213668743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94694712126200347236449981 35510517047325130213668743)
            ·
              refine ⟨53265775570987695320503115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35510517047325130213668743 53265775570987695320503115)
              ·
                refine ⟨79898663356481542980754673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53265775570987695320503115 79898663356481542980754673)
                ·
                  refine ⟨59923997517361157235566005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79898663356481542980754673 59923997517361157235566005)
                  ·
                    refine ⟨5617874767252608490834313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59923997517361157235566005 5617874767252608490834313)
                    ·
                      refine ⟨4213406075439456368125735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617874767252608490834313 4213406075439456368125735)
                      ·
                        rfl

theorem cell23_8205579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 5, 2].length) (baseStart_8205579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205579 prefixEnd_8205579 := by exact prefixLift 8205579
  have htrace : WordTrace (prefixWord ++ tailWord_8205579) baseStart_8205579 baseEnd_8205579 := by
    simpa [prefixWord, tailWord_8205579, baseEnd_8205579] using wordTrace_append hprefix tailTrace_8205579
  have hstable : (prefixWord ++ tailWord_8205579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205579).length < 2 ^ (prefixWord ++ tailWord_8205579).sum := by decide
  have hdescent : baseEnd_8205579 < baseStart_8205579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205632 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 8]
def baseStart_8205632 : Nat := 118140960795 + 8205632 * 2 ^ 59
def prefixEnd_8205632 : Nat := 4983230072969 + 3 ^ 40 * 8205632 * 2
def baseEnd_8205632 : Nat := 468159254434904962306999

theorem tailTrace_8205632 : CollatzResearch.WordTrace tailWord_8205632 prefixEnd_8205632 468159254434904962306999 := by
  unfold tailWord_8205632
  simp only [CollatzResearch.WordTrace]
  refine ⟨149641993104202074609365575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199522657472269432812487433 149641993104202074609365575)
  ·
    refine ⟨224462989656303111914048363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149641993104202074609365575 224462989656303111914048363)
    ·
      refine ⟨336694484484454667871072545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224462989656303111914048363 336694484484454667871072545)
      ·
        refine ⟨252520863363341000903304409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336694484484454667871072545 252520863363341000903304409)
        ·
          refine ⟨189390647522505750677478307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252520863363341000903304409 189390647522505750677478307)
          ·
            refine ⟨284085971283758626016217461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189390647522505750677478307 284085971283758626016217461)
            ·
              refine ⟨26633059807852371189020387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284085971283758626016217461 26633059807852371189020387)
              ·
                refine ⟨39949589711778556783530581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26633059807852371189020387 39949589711778556783530581)
                ·
                  refine ⟨468159254434904962306999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39949589711778556783530581 468159254434904962306999)
                  ·
                    rfl

theorem cell23_8205632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 8].length) (baseStart_8205632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205632 prefixEnd_8205632 := by exact prefixLift 8205632
  have htrace : WordTrace (prefixWord ++ tailWord_8205632) baseStart_8205632 baseEnd_8205632 := by
    simpa [prefixWord, tailWord_8205632, baseEnd_8205632] using wordTrace_append hprefix tailTrace_8205632
  have hstable : (prefixWord ++ tailWord_8205632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205632).length < 2 ^ (prefixWord ++ tailWord_8205632).sum := by decide
  have hdescent : baseEnd_8205632 < baseStart_8205632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205679 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 1, 5]
def baseStart_8205679 : Nat := 118140960795 + 8205679 * 2 ^ 59
def prefixEnd_8205679 : Nat := 4983230072969 + 3 ^ 40 * 8205679 * 2
def baseEnd_8205679 : Nat := 1404485807834968658958425

theorem tailTrace_8205679 : CollatzResearch.WordTrace tailWord_8205679 prefixEnd_8205679 1404485807834968658958425 := by
  unfold tailWord_8205679
  simp only [CollatzResearch.WordTrace]
  refine ⟨299285700439233876245692091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199523800292822584163794727 299285700439233876245692091)
  ·
    refine ⟨448928550658850814368538137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299285700439233876245692091 448928550658850814368538137)
    ·
      refine ⟨336696412994138110776403603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448928550658850814368538137 336696412994138110776403603)
      ·
        refine ⟨505044619491207166164605405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336696412994138110776403603 505044619491207166164605405)
        ·
          refine ⟨189391732309202687311727027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505044619491207166164605405 189391732309202687311727027)
          ·
            refine ⟨284087598463804030967590541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189391732309202687311727027 284087598463804030967590541)
            ·
              refine ⟨106532849423926511612846453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284087598463804030967590541 106532849423926511612846453)
              ·
                refine ⟨9987454633493110463704355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106532849423926511612846453 9987454633493110463704355)
                ·
                  refine ⟨14981181950239665695556533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9987454633493110463704355 14981181950239665695556533)
                  ·
                    refine ⟨1404485807834968658958425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14981181950239665695556533 1404485807834968658958425)
                    ·
                      rfl

theorem cell23_8205679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_8205679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205679 prefixEnd_8205679 := by exact prefixLift 8205679
  have htrace : WordTrace (prefixWord ++ tailWord_8205679) baseStart_8205679 baseEnd_8205679 := by
    simpa [prefixWord, tailWord_8205679, baseEnd_8205679] using wordTrace_append hprefix tailTrace_8205679
  have hstable : (prefixWord ++ tailWord_8205679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205679).length < 2 ^ (prefixWord ++ tailWord_8205679).sum := by decide
  have hdescent : baseEnd_8205679 < baseStart_8205679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205720 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 2, 3, 2]
def baseStart_8205720 : Nat := 118140960795 + 8205720 * 2 ^ 59
def prefixEnd_8205720 : Nat := 4983230072969 + 3 ^ 40 * 8205720 * 2
def baseEnd_8205720 : Nat := 4213478476211740316462587

theorem tailTrace_8205720 : CollatzResearch.WordTrace tailWord_8205720 prefixEnd_8205720 4213478476211740316462587 := by
  unfold tailWord_8205720
  simp only [CollatzResearch.WordTrace]
  refine ⟨149643597916042670123967307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199524797221390226831956409 149643597916042670123967307)
  ·
    refine ⟨224465396874064005185950961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149643597916042670123967307 224465396874064005185950961)
    ·
      refine ⟨168349047655548003889463221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224465396874064005185950961 168349047655548003889463221)
      ·
        refine ⟨15782723217707625364637177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168349047655548003889463221 15782723217707625364637177)
        ·
          refine ⟨11837042413280719023477883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15782723217707625364637177 11837042413280719023477883)
          ·
            refine ⟨17755563619921078535216825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11837042413280719023477883 17755563619921078535216825)
            ·
              refine ⟨13316672714940808901412619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17755563619921078535216825 13316672714940808901412619)
              ·
                refine ⟨19975009072411213352118929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13316672714940808901412619 19975009072411213352118929)
                ·
                  refine ⟨14981256804308410014089197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19975009072411213352118929 14981256804308410014089197)
                  ·
                    refine ⟨5617971301615653755283449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14981256804308410014089197 5617971301615653755283449)
                    ·
                      refine ⟨4213478476211740316462587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5617971301615653755283449 4213478476211740316462587)
                      ·
                        rfl

theorem cell23_8205720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_8205720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205720 prefixEnd_8205720 := by exact prefixLift 8205720
  have htrace : WordTrace (prefixWord ++ tailWord_8205720) baseStart_8205720 baseEnd_8205720 := by
    simpa [prefixWord, tailWord_8205720, baseEnd_8205720] using wordTrace_append hprefix tailTrace_8205720
  have hstable : (prefixWord ++ tailWord_8205720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205720).length < 2 ^ (prefixWord ++ tailWord_8205720).sum := by decide
  have hdescent : baseEnd_8205720 < baseStart_8205720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205930 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_8205930 : Nat := 118140960795 + 8205930 * 2 ^ 59
def prefixEnd_8205930 : Nat := 4983230072969 + 3 ^ 40 * 8205930 * 2
def baseEnd_8205930 : Nat := 4213586307149184494836621

theorem tailTrace_8205930 : CollatzResearch.WordTrace tailWord_8205930 prefixEnd_8205930 4213586307149184494836621 := by
  unfold tailWord_8205930
  simp only [CollatzResearch.WordTrace]
  refine ⟨74823713790331136528269811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199529903440883030742052829 74823713790331136528269811)
  ·
    refine ⟨112235570685496704792404717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74823713790331136528269811 112235570685496704792404717)
    ·
      refine ⟨42088339007061264297151769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112235570685496704792404717 42088339007061264297151769)
      ·
        refine ⟨31566254255295948222863827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42088339007061264297151769 31566254255295948222863827)
        ·
          refine ⟨47349381382943922334295741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31566254255295948222863827 47349381382943922334295741)
          ·
            refine ⟨17756018018603970875360903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47349381382943922334295741 17756018018603970875360903)
            ·
              refine ⟨26634027027905956313041355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17756018018603970875360903 26634027027905956313041355)
              ·
                refine ⟨39951040541858934469562033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26634027027905956313041355 39951040541858934469562033)
                ·
                  refine ⟨29963280406394200852171525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39951040541858934469562033 29963280406394200852171525)
                  ·
                    refine ⟨5618115076198912659782161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29963280406394200852171525 5618115076198912659782161)
                    ·
                      refine ⟨4213586307149184494836621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618115076198912659782161 4213586307149184494836621)
                      ·
                        rfl

theorem cell23_8205930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_8205930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205930 prefixEnd_8205930 := by exact prefixLift 8205930
  have htrace : WordTrace (prefixWord ++ tailWord_8205930) baseStart_8205930 baseEnd_8205930 := by
    simpa [prefixWord, tailWord_8205930, baseEnd_8205930] using wordTrace_append hprefix tailTrace_8205930
  have hstable : (prefixWord ++ tailWord_8205930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205930).length < 2 ^ (prefixWord ++ tailWord_8205930).sum := by decide
  have hdescent : baseEnd_8205930 < baseStart_8205930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205946 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_8205946 : Nat := 118140960795 + 8205946 * 2 ^ 59
def prefixEnd_8205946 : Nat := 4983230072969 + 3 ^ 40 * 8205946 * 2
def baseEnd_8205946 : Nat := 4213594522839656432236547

theorem tailTrace_8205946 : CollatzResearch.WordTrace tailWord_8205946 prefixEnd_8205946 4213594522839656432236547 := by
  unfold tailWord_8205946
  simp only [CollatzResearch.WordTrace]
  refine ⟨74823859682316645211415423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199530292486177720563774461 74823859682316645211415423)
  ·
    refine ⟨112235789523474967817123135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74823859682316645211415423 112235789523474967817123135)
    ·
      refine ⟨168353684285212451725684703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112235789523474967817123135 168353684285212451725684703)
      ·
        refine ⟨252530526427818677588527055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168353684285212451725684703 252530526427818677588527055)
        ·
          refine ⟨378795789641728016382790583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252530526427818677588527055 378795789641728016382790583)
          ·
            refine ⟨568193684462592024574185875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378795789641728016382790583 568193684462592024574185875)
            ·
              refine ⟨852290526693888036861278813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568193684462592024574185875 852290526693888036861278813)
              ·
                refine ⟨319608947510208013822979555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 852290526693888036861278813 319608947510208013822979555)
                ·
                  refine ⟨479413421265312020734469333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319608947510208013822979555 479413421265312020734469333)
                  ·
                    refine ⟨11236252060905750485964125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 479413421265312020734469333 11236252060905750485964125)
                    ·
                      refine ⟨4213594522839656432236547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236252060905750485964125 4213594522839656432236547)
                      ·
                        rfl

theorem cell23_8205946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_8205946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205946 prefixEnd_8205946 := by exact prefixLift 8205946
  have htrace : WordTrace (prefixWord ++ tailWord_8205946) baseStart_8205946 baseEnd_8205946 := by
    simpa [prefixWord, tailWord_8205946, baseEnd_8205946] using wordTrace_append hprefix tailTrace_8205946
  have hstable : (prefixWord ++ tailWord_8205946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205946).length < 2 ^ (prefixWord ++ tailWord_8205946).sum := by decide
  have hdescent : baseEnd_8205946 < baseStart_8205946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8205963 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 3]
def baseStart_8205963 : Nat := 118140960795 + 8205963 * 2 ^ 59
def prefixEnd_8205963 : Nat := 4983230072969 + 3 ^ 40 * 8205963 * 2
def baseEnd_8205963 : Nat := 4213603252010782865723969

theorem tailTrace_8205963 : CollatzResearch.WordTrace tailWord_8205963 prefixEnd_8205963 4213603252010782865723969 := by
  unfold tailWord_8205963
  simp only [CollatzResearch.WordTrace]
  refine ⟨299296058770204992749030543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199530705846803328499353695 299296058770204992749030543)
  ·
    refine ⟨448944088155307489123545815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299296058770204992749030543 448944088155307489123545815)
    ·
      refine ⟨673416132232961233685318723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448944088155307489123545815 673416132232961233685318723)
      ·
        refine ⟨1010124198349441850527978085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673416132232961233685318723 1010124198349441850527978085)
        ·
          refine ⟨189398287190520346973995891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1010124198349441850527978085 189398287190520346973995891)
          ·
            refine ⟨284097430785780520460993837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189398287190520346973995891 284097430785780520460993837)
            ·
              refine ⟨106536536544667695172872689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284097430785780520460993837 106536536544667695172872689)
              ·
                refine ⟨79902402408500771379654517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106536536544667695172872689 79902402408500771379654517)
                ·
                  refine ⟨7490850225796947316842611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79902402408500771379654517 7490850225796947316842611)
                  ·
                    refine ⟨11236275338695420975263917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7490850225796947316842611 11236275338695420975263917)
                    ·
                      refine ⟨4213603252010782865723969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236275338695420975263917 4213603252010782865723969)
                      ·
                        rfl

theorem cell23_8205963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 3].length) (baseStart_8205963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8205963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8205963 prefixEnd_8205963 := by exact prefixLift 8205963
  have htrace : WordTrace (prefixWord ++ tailWord_8205963) baseStart_8205963 baseEnd_8205963 := by
    simpa [prefixWord, tailWord_8205963, baseEnd_8205963] using wordTrace_append hprefix tailTrace_8205963
  have hstable : (prefixWord ++ tailWord_8205963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8205963).length < 2 ^ (prefixWord ++ tailWord_8205963).sum := by decide
  have hdescent : baseEnd_8205963 < baseStart_8205963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8205963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206003 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 2, 6, 2]
def baseStart_8206003 : Nat := 118140960795 + 8206003 * 2 ^ 59
def prefixEnd_8206003 : Nat := 4983230072969 + 3 ^ 40 * 8206003 * 2
def baseEnd_8206003 : Nat := 4213623791236962709223785

theorem tailTrace_8206003 : CollatzResearch.WordTrace tailWord_8206003 prefixEnd_8206003 4213623791236962709223785 := by
  unfold tailWord_8206003
  simp only [CollatzResearch.WordTrace]
  refine ⟨299297517690060079580486663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199531678460040053053657775 299297517690060079580486663)
  ·
    refine ⟨448946276535090119370729995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299297517690060079580486663 448946276535090119370729995)
    ·
      refine ⟨673419414802635179056094993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448946276535090119370729995 673419414802635179056094993)
      ·
        refine ⟨505064561101976384292071245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673419414802635179056094993 505064561101976384292071245)
        ·
          refine ⟨189399210413241144109526717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505064561101976384292071245 189399210413241144109526717)
          ·
            refine ⟨71024703904965429041072519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189399210413241144109526717 71024703904965429041072519)
            ·
              refine ⟨106537055857448143561608779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71024703904965429041072519 106537055857448143561608779)
              ·
                refine ⟨159805583786172215342413169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106537055857448143561608779 159805583786172215342413169)
                ·
                  refine ⟨119854187839629161506809877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159805583786172215342413169 119854187839629161506809877)
                  ·
                    refine ⟨5618165054982616945631713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119854187839629161506809877 5618165054982616945631713)
                    ·
                      refine ⟨4213623791236962709223785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618165054982616945631713 4213623791236962709223785)
                      ·
                        rfl

theorem cell23_8206003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 6, 2].length) (baseStart_8206003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206003 prefixEnd_8206003 := by exact prefixLift 8206003
  have htrace : WordTrace (prefixWord ++ tailWord_8206003) baseStart_8206003 baseEnd_8206003 := by
    simpa [prefixWord, tailWord_8206003, baseEnd_8206003] using wordTrace_append hprefix tailTrace_8206003
  have hstable : (prefixWord ++ tailWord_8206003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206003).length < 2 ^ (prefixWord ++ tailWord_8206003).sum := by decide
  have hdescent : baseEnd_8206003 < baseStart_8206003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206013 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_8206013 : Nat := 118140960795 + 8206013 * 2 ^ 59
def prefixEnd_8206013 : Nat := 4983230072969 + 3 ^ 40 * 8206013 * 2
def baseEnd_8206013 : Nat := 1404542975347835890032913

theorem tailTrace_8206013 : CollatzResearch.WordTrace tailWord_8206013 prefixEnd_8206013 1404542975347835890032913 := by
  unfold tailWord_8206013
  simp only [CollatzResearch.WordTrace]
  refine ⟨299297882420023851288350693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199531921613349234192233795 299297882420023851288350693)
  ·
    refine ⟨56118352953754472116565755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299297882420023851288350693 56118352953754472116565755)
    ·
      refine ⟨84177529430631708174848633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56118352953754472116565755 84177529430631708174848633)
      ·
        refine ⟨63133147072973781131136475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84177529430631708174848633 63133147072973781131136475)
        ·
          refine ⟨94699720609460671696704713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63133147072973781131136475 94699720609460671696704713)
          ·
            refine ⟨71024790457095503772528535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94699720609460671696704713 71024790457095503772528535)
            ·
              refine ⟨106537185685643255658792803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71024790457095503772528535 106537185685643255658792803)
              ·
                refine ⟨159805778528464883488189205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106537185685643255658792803 159805778528464883488189205)
                ·
                  refine ⟨7490895868521791413508869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159805778528464883488189205 7490895868521791413508869)
                  ·
                    refine ⟨1404542975347835890032913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7490895868521791413508869 1404542975347835890032913)
                    ·
                      rfl

theorem cell23_8206013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_8206013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206013 prefixEnd_8206013 := by exact prefixLift 8206013
  have htrace : WordTrace (prefixWord ++ tailWord_8206013) baseStart_8206013 baseEnd_8206013 := by
    simpa [prefixWord, tailWord_8206013, baseEnd_8206013] using wordTrace_append hprefix tailTrace_8206013
  have hstable : (prefixWord ++ tailWord_8206013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206013).length < 2 ^ (prefixWord ++ tailWord_8206013).sum := by decide
  have hdescent : baseEnd_8206013 < baseStart_8206013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206014 : List Nat := [4, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_8206014 : Nat := 118140960795 + 8206014 * 2 ^ 59
def prefixEnd_8206014 : Nat := 4983230072969 + 3 ^ 40 * 8206014 * 2
def baseEnd_8206014 : Nat := 4213629439524162166186235

theorem tailTrace_8206014 : CollatzResearch.WordTrace tailWord_8206014 prefixEnd_8206014 4213629439524162166186235 := by
  unfold tailWord_8206014
  simp only [CollatzResearch.WordTrace]
  refine ⟨37412239861627528557392137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199531945928680152306091397 37412239861627528557392137)
  ·
    refine ⟨28059179896220646418044103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37412239861627528557392137 28059179896220646418044103)
    ·
      refine ⟨42088769844330969627066155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28059179896220646418044103 42088769844330969627066155)
      ·
        refine ⟨63133154766496454440599233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42088769844330969627066155 63133154766496454440599233)
        ·
          refine ⟨47349866074872340830449425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63133154766496454440599233 47349866074872340830449425)
          ·
            refine ⟨35512399556154255622837069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47349866074872340830449425 35512399556154255622837069)
            ·
              refine ⟨13317149833557845858563901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35512399556154255622837069 13317149833557845858563901)
              ·
                refine ⟨4993931187584192196961463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13317149833557845858563901 4993931187584192196961463)
                ·
                  refine ⟨7490896781376288295442195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993931187584192196961463 7490896781376288295442195)
                  ·
                    refine ⟨11236345172064432443163293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7490896781376288295442195 11236345172064432443163293)
                    ·
                      refine ⟨4213629439524162166186235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236345172064432443163293 4213629439524162166186235)
                      ·
                        rfl

theorem cell23_8206014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_8206014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206014 prefixEnd_8206014 := by exact prefixLift 8206014
  have htrace : WordTrace (prefixWord ++ tailWord_8206014) baseStart_8206014 baseEnd_8206014 := by
    simpa [prefixWord, tailWord_8206014, baseEnd_8206014] using wordTrace_append hprefix tailTrace_8206014
  have hstable : (prefixWord ++ tailWord_8206014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206014).length < 2 ^ (prefixWord ++ tailWord_8206014).sum := by decide
  have hdescent : baseEnd_8206014 < baseStart_8206014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206020 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_8206020 : Nat := 118140960795 + 8206020 * 2 ^ 59
def prefixEnd_8206020 : Nat := 4983230072969 + 3 ^ 40 * 8206020 * 2
def baseEnd_8206020 : Nat := 4213632520408089142711207

theorem tailTrace_8206020 : CollatzResearch.WordTrace tailWord_8206020 prefixEnd_8206020 4213632520408089142711207 := by
  unfold tailWord_8206020
  simp only [CollatzResearch.WordTrace]
  refine ⟨149649068865499245741927757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199532091820665660989237009 149649068865499245741927757)
  ·
    refine ⟨56118400824562217153222909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149649068865499245741927757 56118400824562217153222909)
    ·
      refine ⟨21044400309210831432458591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56118400824562217153222909 21044400309210831432458591)
      ·
        refine ⟨31566600463816247148687887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21044400309210831432458591 31566600463816247148687887)
        ·
          refine ⟨47349900695724370723031831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31566600463816247148687887 47349900695724370723031831)
          ·
            refine ⟨71024851043586556084547747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47349900695724370723031831 71024851043586556084547747)
            ·
              refine ⟨106537276565379834126821621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71024851043586556084547747 106537276565379834126821621)
              ·
                refine ⟨9987869678004359449389527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106537276565379834126821621 9987869678004359449389527)
                ·
                  refine ⟨14981804517006539174084291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9987869678004359449389527 14981804517006539174084291)
                  ·
                    refine ⟨22472706775509808761126437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14981804517006539174084291 22472706775509808761126437)
                    ·
                      refine ⟨4213632520408089142711207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22472706775509808761126437 4213632520408089142711207)
                      ·
                        rfl

theorem cell23_8206020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_8206020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206020 prefixEnd_8206020 := by exact prefixLift 8206020
  have htrace : WordTrace (prefixWord ++ tailWord_8206020) baseStart_8206020 baseEnd_8206020 := by
    simpa [prefixWord, tailWord_8206020, baseEnd_8206020] using wordTrace_append hprefix tailTrace_8206020
  have hstable : (prefixWord ++ tailWord_8206020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206020).length < 2 ^ (prefixWord ++ tailWord_8206020).sum := by decide
  have hdescent : baseEnd_8206020 < baseStart_8206020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206023 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_8206023 : Nat := 118140960795 + 8206023 * 2 ^ 59
def prefixEnd_8206023 : Nat := 4983230072969 + 3 ^ 40 * 8206023 * 2
def baseEnd_8206023 : Nat := 4213634060850052630973693

theorem tailTrace_8206023 : CollatzResearch.WordTrace tailWord_8206023 prefixEnd_8206023 4213634060850052630973693 := by
  unfold tailWord_8206023
  simp only [CollatzResearch.WordTrace]
  refine ⟨299298247149987622996214723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199532164766658415330809815 299298247149987622996214723)
  ·
    refine ⟨448947370724981434494322085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299298247149987622996214723 448947370724981434494322085)
    ·
      refine ⟨84177632010934018967685391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448947370724981434494322085 84177632010934018967685391)
      ·
        refine ⟨126266448016401028451528087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84177632010934018967685391 126266448016401028451528087)
        ·
          refine ⟨189399672024601542677292131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126266448016401028451528087 189399672024601542677292131)
          ·
            refine ⟨284099508036902314015938197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189399672024601542677292131 284099508036902314015938197)
            ·
              refine ⟨13317164439229795969497103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284099508036902314015938197 13317164439229795969497103)
              ·
                refine ⟨19975746658844693954245655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13317164439229795969497103 19975746658844693954245655)
                ·
                  refine ⟨29963619988267040931368483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19975746658844693954245655 29963619988267040931368483)
                  ·
                    refine ⟨44945429982400561397052725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29963619988267040931368483 44945429982400561397052725)
                    ·
                      refine ⟨4213634060850052630973693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44945429982400561397052725 4213634060850052630973693)
                      ·
                        rfl

theorem cell23_8206023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_8206023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206023 prefixEnd_8206023 := by exact prefixLift 8206023
  have htrace : WordTrace (prefixWord ++ tailWord_8206023) baseStart_8206023 baseEnd_8206023 := by
    simpa [prefixWord, tailWord_8206023, baseEnd_8206023] using wordTrace_append hprefix tailTrace_8206023
  have hstable : (prefixWord ++ tailWord_8206023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206023).length < 2 ^ (prefixWord ++ tailWord_8206023).sum := by decide
  have hdescent : baseEnd_8206023 < baseStart_8206023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206030 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_8206030 : Nat := 118140960795 + 8206030 * 2 ^ 59
def prefixEnd_8206030 : Nat := 4983230072969 + 3 ^ 40 * 8206030 * 2
def baseEnd_8206030 : Nat := 1404545885071544701195387

theorem tailTrace_8206030 : CollatzResearch.WordTrace tailWord_8206030 prefixEnd_8206030 1404545885071544701195387 := by
  unfold tailWord_8206030
  simp only [CollatzResearch.WordTrace]
  refine ⟨37412312807620282898964943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199532334973974842127813029 37412312807620282898964943)
  ·
    refine ⟨56118469211430424348447415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37412312807620282898964943 56118469211430424348447415)
    ·
      refine ⟨84177703817145636522671123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56118469211430424348447415 84177703817145636522671123)
      ·
        refine ⟨126266555725718454784006685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84177703817145636522671123 126266555725718454784006685)
        ·
          refine ⟨47349958397144420544002507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126266555725718454784006685 47349958397144420544002507)
          ·
            refine ⟨71024937595716630816003761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47349958397144420544002507 71024937595716630816003761)
            ·
              refine ⟨53268703196787473112002821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71024937595716630816003761 53268703196787473112002821)
              ·
                refine ⟨9987881849397651208500529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53268703196787473112002821 9987881849397651208500529)
                ·
                  refine ⟨7490911387048238406375397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9987881849397651208500529 7490911387048238406375397)
                  ·
                    refine ⟨1404545885071544701195387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7490911387048238406375397 1404545885071544701195387)
                    ·
                      rfl

theorem cell23_8206030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_8206030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206030 prefixEnd_8206030 := by exact prefixLift 8206030
  have htrace : WordTrace (prefixWord ++ tailWord_8206030) baseStart_8206030 baseEnd_8206030 := by
    simpa [prefixWord, tailWord_8206030, baseEnd_8206030] using wordTrace_append hprefix tailTrace_8206030
  have hstable : (prefixWord ++ tailWord_8206030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206030).length < 2 ^ (prefixWord ++ tailWord_8206030).sum := by decide
  have hdescent : baseEnd_8206030 < baseStart_8206030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206070 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_8206070 : Nat := 118140960795 + 8206070 * 2 ^ 59
def prefixEnd_8206070 : Nat := 4983230072969 + 3 ^ 40 * 8206070 * 2
def baseEnd_8206070 : Nat := 4213658194440813947085977

theorem tailTrace_8206070 : CollatzResearch.WordTrace tailWord_8206070 prefixEnd_8206070 4213658194440813947085977 := by
  unfold tailWord_8206070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18706247586301084376448479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199533307587211566682117109 18706247586301084376448479)
  ·
    refine ⟨28059371379451626564672719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18706247586301084376448479 28059371379451626564672719)
    ·
      refine ⟨42089057069177439847009079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28059371379451626564672719 42089057069177439847009079)
      ·
        refine ⟨63133585603766159770513619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42089057069177439847009079 63133585603766159770513619)
        ·
          refine ⟨94700378405649239655770429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63133585603766159770513619 94700378405649239655770429)
          ·
            refine ⟨35512641902118464870913911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94700378405649239655770429 35512641902118464870913911)
            ·
              refine ⟨53268962853177697306370867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35512641902118464870913911 53268962853177697306370867)
              ·
                refine ⟨79903444279766545959556301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53268962853177697306370867 79903444279766545959556301)
                ·
                  refine ⟨29963791604912454734833613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79903444279766545959556301 29963791604912454734833613)
                  ·
                    refine ⟨11236421851842170525562605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29963791604912454734833613 11236421851842170525562605)
                    ·
                      refine ⟨4213658194440813947085977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236421851842170525562605 4213658194440813947085977)
                      ·
                        rfl

theorem cell23_8206070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_8206070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206070 prefixEnd_8206070 := by exact prefixLift 8206070
  have htrace : WordTrace (prefixWord ++ tailWord_8206070) baseStart_8206070 baseEnd_8206070 := by
    simpa [prefixWord, tailWord_8206070, baseEnd_8206070] using wordTrace_append hprefix tailTrace_8206070
  have hstable : (prefixWord ++ tailWord_8206070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206070).length < 2 ^ (prefixWord ++ tailWord_8206070).sum := by decide
  have hdescent : baseEnd_8206070 < baseStart_8206070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206103 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 1, 8]
def baseStart_8206103 : Nat := 118140960795 + 8206103 * 2 ^ 59
def prefixEnd_8206103 : Nat := 4983230072969 + 3 ^ 40 * 8206103 * 2
def baseEnd_8206103 : Nat := 1404558379767470772657775

theorem tailTrace_8206103 : CollatzResearch.WordTrace tailWord_8206103 prefixEnd_8206103 1404558379767470772657775 := by
  unfold tailWord_8206103
  simp only [CollatzResearch.WordTrace]
  refine ⟨299301164989697796659126963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199534109993131864439417975 299301164989697796659126963)
  ·
    refine ⟨448951747484546694988690445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299301164989697796659126963 448951747484546694988690445)
    ·
      refine ⟨168356905306705010620758917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448951747484546694988690445 168356905306705010620758917)
      ·
        refine ⟨31566919745007189491392297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168356905306705010620758917 31566919745007189491392297)
        ·
          refine ⟨23675189808755392118544223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31566919745007189491392297 23675189808755392118544223)
          ·
            refine ⟨35512784713133088177816335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23675189808755392118544223 35512784713133088177816335)
            ·
              refine ⟨53269177069699632266724503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35512784713133088177816335 53269177069699632266724503)
              ·
                refine ⟨79903765604549448400086755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53269177069699632266724503 79903765604549448400086755)
                ·
                  refine ⟨119855648406824172600130133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79903765604549448400086755 119855648406824172600130133)
                  ·
                    refine ⟨1404558379767470772657775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119855648406824172600130133 1404558379767470772657775)
                    ·
                      rfl

theorem cell23_8206103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_8206103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206103 prefixEnd_8206103 := by exact prefixLift 8206103
  have htrace : WordTrace (prefixWord ++ tailWord_8206103) baseStart_8206103 baseEnd_8206103 := by
    simpa [prefixWord, tailWord_8206103, baseEnd_8206103] using wordTrace_append hprefix tailTrace_8206103
  have hstable : (prefixWord ++ tailWord_8206103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206103).length < 2 ^ (prefixWord ++ tailWord_8206103).sum := by decide
  have hdescent : baseEnd_8206103 < baseStart_8206103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206131 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 1, 3, 2]
def baseStart_8206131 : Nat := 118140960795 + 8206131 * 2 ^ 59
def prefixEnd_8206131 : Nat := 4983230072969 + 3 ^ 40 * 8206131 * 2
def baseEnd_8206131 : Nat := 4213689516760738208423197

theorem tailTrace_8206131 : CollatzResearch.WordTrace tailWord_8206131 prefixEnd_8206131 4213689516760738208423197 := by
  unfold tailWord_8206131
  simp only [CollatzResearch.WordTrace]
  refine ⟨299302186233596357441146247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199534790822397571627430831 299302186233596357441146247)
  ·
    refine ⟨448953279350394536161719371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299302186233596357441146247 448953279350394536161719371)
    ·
      refine ⟨673429919025591804242579057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448953279350394536161719371 673429919025591804242579057)
      ·
        refine ⟨505072439269193853181934293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673429919025591804242579057 505072439269193853181934293)
        ·
          refine ⟨11837635295371730933951585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 505072439269193853181934293 11837635295371730933951585)
          ·
            refine ⟨8878226471528798200463689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11837635295371730933951585 8878226471528798200463689)
            ·
              refine ⟨6658669853646598650347767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8878226471528798200463689 6658669853646598650347767)
              ·
                refine ⟨9988004780469897975521651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658669853646598650347767 9988004780469897975521651)
                ·
                  refine ⟨14982007170704846963282477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9988004780469897975521651 14982007170704846963282477)
                  ·
                    refine ⟨5618252689014317611230929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14982007170704846963282477 5618252689014317611230929)
                    ·
                      refine ⟨4213689516760738208423197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618252689014317611230929 4213689516760738208423197)
                      ·
                        rfl

theorem cell23_8206131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 3, 2].length) (baseStart_8206131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206131 prefixEnd_8206131 := by exact prefixLift 8206131
  have htrace : WordTrace (prefixWord ++ tailWord_8206131) baseStart_8206131 baseEnd_8206131 := by
    simpa [prefixWord, tailWord_8206131, baseEnd_8206131] using wordTrace_append hprefix tailTrace_8206131
  have hstable : (prefixWord ++ tailWord_8206131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206131).length < 2 ^ (prefixWord ++ tailWord_8206131).sum := by decide
  have hdescent : baseEnd_8206131 < baseStart_8206131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206157 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_8206157 : Nat := 118140960795 + 8206157 * 2 ^ 59
def prefixEnd_8206157 : Nat := 4983230072969 + 3 ^ 40 * 8206157 * 2
def baseEnd_8206157 : Nat := 4213702867257755106698077

theorem tailTrace_8206157 : CollatzResearch.WordTrace tailWord_8206157 prefixEnd_8206157 4213702867257755106698077 := by
  unfold tailWord_8206157
  simp only [CollatzResearch.WordTrace]
  refine ⟨299303134531502163881592725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199535423021001442587728483 299303134531502163881592725)
  ·
    refine ⟨14029834431164163931949659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 299303134531502163881592725 14029834431164163931949659)
    ·
      refine ⟨21044751646746245897924489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14029834431164163931949659 21044751646746245897924489)
      ·
        refine ⟨15783563735059684423443367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21044751646746245897924489 15783563735059684423443367)
        ·
          refine ⟨23675345602589526635165051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15783563735059684423443367 23675345602589526635165051)
          ·
            refine ⟨35513018403884289952747577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23675345602589526635165051 35513018403884289952747577)
            ·
              refine ⟨26634763802913217464560683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35513018403884289952747577 26634763802913217464560683)
              ·
                refine ⟨39952145704369826196841025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26634763802913217464560683 39952145704369826196841025)
                ·
                  refine ⟨29964109278277369647630769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39952145704369826196841025 29964109278277369647630769)
                  ·
                    refine ⟨22473081958708027235723077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29964109278277369647630769 22473081958708027235723077)
                    ·
                      refine ⟨4213702867257755106698077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22473081958708027235723077 4213702867257755106698077)
                      ·
                        rfl

theorem cell23_8206157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_8206157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206157 prefixEnd_8206157 := by exact prefixLift 8206157
  have htrace : WordTrace (prefixWord ++ tailWord_8206157) baseStart_8206157 baseEnd_8206157 := by
    simpa [prefixWord, tailWord_8206157, baseEnd_8206157] using wordTrace_append hprefix tailTrace_8206157
  have hstable : (prefixWord ++ tailWord_8206157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206157).length < 2 ^ (prefixWord ++ tailWord_8206157).sum := by decide
  have hdescent : baseEnd_8206157 < baseStart_8206157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206161 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 2, 2, 2]
def baseStart_8206161 : Nat := 118140960795 + 8206161 * 2 ^ 59
def prefixEnd_8206161 : Nat := 4983230072969 + 3 ^ 40 * 8206161 * 2
def baseEnd_8206161 : Nat := 4213704921180373091048059

theorem tailTrace_8206161 : CollatzResearch.WordTrace tailWord_8206161 prefixEnd_8206161 4213704921180373091048059 := by
  unfold tailWord_8206161
  simp only [CollatzResearch.WordTrace]
  refine ⟨299303280423487672564738337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199535520282325115043158891 299303280423487672564738337)
  ·
    refine ⟨224477460317615754423553753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299303280423487672564738337 224477460317615754423553753)
    ·
      refine ⟨168358095238211815817665315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224477460317615754423553753 168358095238211815817665315)
      ·
        refine ⟨252537142857317723726497973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168358095238211815817665315 252537142857317723726497973)
        ·
          refine ⟨23675357142873536599359185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252537142857317723726497973 23675357142873536599359185)
          ·
            refine ⟨17756517857155152449519389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23675357142873536599359185 17756517857155152449519389)
            ·
              refine ⟨6658694196433182168569771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17756517857155152449519389 6658694196433182168569771)
              ·
                refine ⟨9988041294649773252854657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658694196433182168569771 9988041294649773252854657)
                ·
                  refine ⟨7491030970987329939640993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9988041294649773252854657 7491030970987329939640993)
                  ·
                    refine ⟨5618273228240497454730745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7491030970987329939640993 5618273228240497454730745)
                    ·
                      refine ⟨4213704921180373091048059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618273228240497454730745 4213704921180373091048059)
                      ·
                        rfl

theorem cell23_8206161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_8206161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206161 prefixEnd_8206161 := by exact prefixLift 8206161
  have htrace : WordTrace (prefixWord ++ tailWord_8206161) baseStart_8206161 baseEnd_8206161 := by
    simpa [prefixWord, tailWord_8206161, baseEnd_8206161] using wordTrace_append hprefix tailTrace_8206161
  have hstable : (prefixWord ++ tailWord_8206161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206161).length < 2 ^ (prefixWord ++ tailWord_8206161).sum := by decide
  have hdescent : baseEnd_8206161 < baseStart_8206161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206220 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_8206220 : Nat := 118140960795 + 8206220 * 2 ^ 59
def prefixEnd_8206220 : Nat := 4983230072969 + 3 ^ 40 * 8206220 * 2
def baseEnd_8206220 : Nat := 4213735216538988360210287

theorem tailTrace_8206220 : CollatzResearch.WordTrace tailWord_8206220 prefixEnd_8206220 4213735216538988360210287 := by
  unfold tailWord_8206220
  simp only [CollatzResearch.WordTrace]
  refine ⟨149652716165136962820568057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199536954886849283760757409 149652716165136962820568057)
  ·
    refine ⟨112239537123852722115426043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149652716165136962820568057 112239537123852722115426043)
    ·
      refine ⟨168359305685779083173139065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112239537123852722115426043 168359305685779083173139065)
      ·
        refine ⟨126269479264334312379854299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168359305685779083173139065 126269479264334312379854299)
        ·
          refine ⟨189404218896501468569781449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126269479264334312379854299 189404218896501468569781449)
          ·
            refine ⟨142053164172376101427336087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189404218896501468569781449 142053164172376101427336087)
            ·
              refine ⟨213079746258564152141004131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142053164172376101427336087 213079746258564152141004131)
              ·
                refine ⟨319619619387846228211506197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213079746258564152141004131 319619619387846228211506197)
                ·
                  refine ⟨14982169658805291947414353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319619619387846228211506197 14982169658805291947414353)
                  ·
                    refine ⟨11236627244103968960560765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14982169658805291947414353 11236627244103968960560765)
                    ·
                      refine ⟨4213735216538988360210287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236627244103968960560765 4213735216538988360210287)
                      ·
                        rfl

theorem cell23_8206220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_8206220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206220 prefixEnd_8206220 := by exact prefixLift 8206220
  have htrace : WordTrace (prefixWord ++ tailWord_8206220) baseStart_8206220 baseEnd_8206220 := by
    simpa [prefixWord, tailWord_8206220, baseEnd_8206220] using wordTrace_append hprefix tailTrace_8206220
  have hstable : (prefixWord ++ tailWord_8206220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206220).length < 2 ^ (prefixWord ++ tailWord_8206220).sum := by decide
  have hdescent : baseEnd_8206220 < baseStart_8206220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206237 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_8206237 : Nat := 118140960795 + 8206237 * 2 ^ 59
def prefixEnd_8206237 : Nat := 4983230072969 + 3 ^ 40 * 8206237 * 2
def baseEnd_8206237 : Nat := 4213743945710114793697709

theorem tailTrace_8206237 : CollatzResearch.WordTrace tailWord_8206237 prefixEnd_8206237 4213743945710114793697709 := by
  unfold tailWord_8206237
  simp only [CollatzResearch.WordTrace]
  refine ⟨299306052371212337544504965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199537368247474891696336643 299306052371212337544504965)
  ·
    refine ⟨56119884819602313289594681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299306052371212337544504965 56119884819602313289594681)
    ·
      refine ⟨42089913614701734967196011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56119884819602313289594681 42089913614701734967196011)
      ·
        refine ⟨63134870422052602450794017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42089913614701734967196011 63134870422052602450794017)
        ·
          refine ⟨47351152816539451838095513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63134870422052602450794017 47351152816539451838095513)
          ·
            refine ⟨35513364612404588878571635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47351152816539451838095513 35513364612404588878571635)
            ·
              refine ⟨53270046918606883317857453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35513364612404588878571635 53270046918606883317857453)
              ·
                refine ⟨19976267594477581244196545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53270046918606883317857453 19976267594477581244196545)
                ·
                  refine ⟨14982200695858185933147409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19976267594477581244196545 14982200695858185933147409)
                  ·
                    refine ⟨11236650521893639449860557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14982200695858185933147409 11236650521893639449860557)
                    ·
                      refine ⟨4213743945710114793697709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236650521893639449860557 4213743945710114793697709)
                      ·
                        rfl

theorem cell23_8206237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_8206237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206237 prefixEnd_8206237 := by exact prefixLift 8206237
  have htrace : WordTrace (prefixWord ++ tailWord_8206237) baseStart_8206237 baseEnd_8206237 := by
    simpa [prefixWord, tailWord_8206237, baseEnd_8206237] using wordTrace_append hprefix tailTrace_8206237
  have hstable : (prefixWord ++ tailWord_8206237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206237).length < 2 ^ (prefixWord ++ tailWord_8206237).sum := by decide
  have hdescent : baseEnd_8206237 < baseStart_8206237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206243 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 8]
def baseStart_8206243 : Nat := 118140960795 + 8206243 * 2 ^ 59
def prefixEnd_8206243 : Nat := 4983230072969 + 3 ^ 40 * 8206243 * 2
def baseEnd_8206243 : Nat := 4213747026594041770222681

theorem tailTrace_8206243 : CollatzResearch.WordTrace tailWord_8206243 prefixEnd_8206243 4213747026594041770222681 := by
  unfold tailWord_8206243
  simp only [CollatzResearch.WordTrace]
  refine ⟨299306271209190600569223383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199537514139460400379482255 299306271209190600569223383)
  ·
    refine ⟨448959406813785900853835075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299306271209190600569223383 448959406813785900853835075)
    ·
      refine ⟨673439110220678851280752613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448959406813785900853835075 673439110220678851280752613)
      ·
        refine ⟨126269833166377284615141115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 673439110220678851280752613 126269833166377284615141115)
        ·
          refine ⟨189404749749565926922711673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126269833166377284615141115 189404749749565926922711673)
          ·
            refine ⟨142053562312174445192033755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189404749749565926922711673 142053562312174445192033755)
            ·
              refine ⟨213080343468261667788050633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142053562312174445192033755 213080343468261667788050633)
              ·
                refine ⟨159810257601196250841037975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213080343468261667788050633 159810257601196250841037975)
                ·
                  refine ⟨239715386401794376261556963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159810257601196250841037975 239715386401794376261556963)
                  ·
                    refine ⟨359573079602691564392335445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239715386401794376261556963 359573079602691564392335445)
                    ·
                      refine ⟨4213747026594041770222681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 359573079602691564392335445 4213747026594041770222681)
                      ·
                        rfl

theorem cell23_8206243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_8206243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206243 prefixEnd_8206243 := by exact prefixLift 8206243
  have htrace : WordTrace (prefixWord ++ tailWord_8206243) baseStart_8206243 baseEnd_8206243 := by
    simpa [prefixWord, tailWord_8206243, baseEnd_8206243] using wordTrace_append hprefix tailTrace_8206243
  have hstable : (prefixWord ++ tailWord_8206243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206243).length < 2 ^ (prefixWord ++ tailWord_8206243).sum := by decide
  have hdescent : baseEnd_8206243 < baseStart_8206243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206257 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 6]
def baseStart_8206257 : Nat := 118140960795 + 8206257 * 2 ^ 59
def prefixEnd_8206257 : Nat := 4983230072969 + 3 ^ 40 * 8206257 * 2
def baseEnd_8206257 : Nat := 468194912813689412827513

theorem tailTrace_8206257 : CollatzResearch.WordTrace tailWord_8206257 prefixEnd_8206257 468194912813689412827513 := by
  unfold tailWord_8206257
  simp only [CollatzResearch.WordTrace]
  refine ⟨299306781831139880960233025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199537854554093253973488683 299306781831139880960233025)
  ·
    refine ⟨224480086373354910720174769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299306781831139880960233025 224480086373354910720174769)
    ·
      refine ⟨168360064780016183040131077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224480086373354910720174769 168360064780016183040131077)
      ·
        refine ⟨31567512146253034320024577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168360064780016183040131077 31567512146253034320024577)
        ·
          refine ⟨23675634109689775740018433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31567512146253034320024577 23675634109689775740018433)
          ·
            refine ⟨17756725582267331805013825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23675634109689775740018433 17756725582267331805013825)
            ·
              refine ⟨13317544186700498853760369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17756725582267331805013825 13317544186700498853760369)
              ·
                refine ⟨9988158140025374140320277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13317544186700498853760369 9988158140025374140320277)
                ·
                  refine ⟨468194912813689412827513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9988158140025374140320277 468194912813689412827513)
                  ·
                    rfl

theorem cell23_8206257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 6].length) (baseStart_8206257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206257 prefixEnd_8206257 := by exact prefixLift 8206257
  have htrace : WordTrace (prefixWord ++ tailWord_8206257) baseStart_8206257 baseEnd_8206257 := by
    simpa [prefixWord, tailWord_8206257, baseEnd_8206257] using wordTrace_append hprefix tailTrace_8206257
  have hstable : (prefixWord ++ tailWord_8206257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206257).length < 2 ^ (prefixWord ++ tailWord_8206257).sum := by decide
  have hdescent : baseEnd_8206257 < baseStart_8206257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206261 : List Nat := [1, 3, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_8206261 : Nat := 118140960795 + 8206261 * 2 ^ 59
def prefixEnd_8206261 : Nat := 4983230072969 + 3 ^ 40 * 8206261 * 2
def baseEnd_8206261 : Nat := 1404585423081940899932533

theorem tailTrace_8206261 : CollatzResearch.WordTrace tailWord_8206261 prefixEnd_8206261 1404585423081940899932533 := by
  unfold tailWord_8206261
  simp only [CollatzResearch.WordTrace]
  refine ⟨299306927723125389643378637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199537951815416926428919091 299306927723125389643378637)
  ·
    refine ⟨112240097896172021116266989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299306927723125389643378637 112240097896172021116266989)
    ·
      refine ⟨42090036711064507918600121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112240097896172021116266989 42090036711064507918600121)
      ·
        refine ⟨31567527533298380938950091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42090036711064507918600121 31567527533298380938950091)
        ·
          refine ⟨47351291299947571408425137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31567527533298380938950091 47351291299947571408425137)
          ·
            refine ⟨35513468474960678556318853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47351291299947571408425137 35513468474960678556318853)
            ·
              refine ⟨6658775339055127229309785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35513468474960678556318853 6658775339055127229309785)
              ·
                refine ⟨4994081504291345421982339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658775339055127229309785 4994081504291345421982339)
                ·
                  refine ⟨7491122256437018132973509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994081504291345421982339 7491122256437018132973509)
                  ·
                    refine ⟨1404585423081940899932533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7491122256437018132973509 1404585423081940899932533)
                    ·
                      rfl

theorem cell23_8206261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_8206261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206261 prefixEnd_8206261 := by exact prefixLift 8206261
  have htrace : WordTrace (prefixWord ++ tailWord_8206261) baseStart_8206261 baseEnd_8206261 := by
    simpa [prefixWord, tailWord_8206261, baseEnd_8206261] using wordTrace_append hprefix tailTrace_8206261
  have hstable : (prefixWord ++ tailWord_8206261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206261).length < 2 ^ (prefixWord ++ tailWord_8206261).sum := by decide
  have hdescent : baseEnd_8206261 < baseStart_8206261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206284 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_8206284 : Nat := 118140960795 + 8206284 * 2 ^ 59
def prefixEnd_8206284 : Nat := 4983230072969 + 3 ^ 40 * 8206284 * 2
def baseEnd_8206284 : Nat := 4213768079300876109809993

theorem tailTrace_8206284 : CollatzResearch.WordTrace tailWord_8206284 prefixEnd_8206284 4213768079300876109809993 := by
  unfold tailWord_8206284
  simp only [CollatzResearch.WordTrace]
  refine ⟨149653883301021032285732953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199538511068028043047643937 149653883301021032285732953)
  ·
    refine ⟨112240412475765774214299715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149653883301021032285732953 112240412475765774214299715)
    ·
      refine ⟨168360618713648661321449573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112240412475765774214299715 168360618713648661321449573)
      ·
        refine ⟨31567616008809123997771795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168360618713648661321449573 31567616008809123997771795)
        ·
          refine ⟨47351424013213685996657693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31567616008809123997771795 47351424013213685996657693)
          ·
            refine ⟨17756784004955132248746635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47351424013213685996657693 17756784004955132248746635)
            ·
              refine ⟨26635176007432698373119953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17756784004955132248746635 26635176007432698373119953)
              ·
                refine ⟨19976382005574523779839965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26635176007432698373119953 19976382005574523779839965)
                ·
                  refine ⟨7491143252090446417439987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19976382005574523779839965 7491143252090446417439987)
                  ·
                    refine ⟨11236714878135669626159981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7491143252090446417439987 11236714878135669626159981)
                    ·
                      refine ⟨4213768079300876109809993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236714878135669626159981 4213768079300876109809993)
                      ·
                        rfl

theorem cell23_8206284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_8206284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206284 prefixEnd_8206284 := by exact prefixLift 8206284
  have htrace : WordTrace (prefixWord ++ tailWord_8206284) baseStart_8206284 baseEnd_8206284 := by
    simpa [prefixWord, tailWord_8206284, baseEnd_8206284] using wordTrace_append hprefix tailTrace_8206284
  have hstable : (prefixWord ++ tailWord_8206284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206284).length < 2 ^ (prefixWord ++ tailWord_8206284).sum := by decide
  have hdescent : baseEnd_8206284 < baseStart_8206284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206320 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_8206320 : Nat := 118140960795 + 8206320 * 2 ^ 59
def prefixEnd_8206320 : Nat := 4983230072969 + 3 ^ 40 * 8206320 * 2
def baseEnd_8206320 : Nat := 4213786564604437968959827

theorem tailTrace_8206320 : CollatzResearch.WordTrace tailWord_8206320 prefixEnd_8206320 4213786564604437968959827 := by
  unfold tailWord_8206320
  simp only [CollatzResearch.WordTrace]
  refine ⟨149654539814955821359888207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199539386419941095146517609 149654539814955821359888207)
  ·
    refine ⟨224481809722433732039832311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149654539814955821359888207 224481809722433732039832311)
    ·
      refine ⟨336722714583650598059748467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224481809722433732039832311 336722714583650598059748467)
      ·
        refine ⟨505084071875475897089622701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336722714583650598059748467 505084071875475897089622701)
        ·
          refine ⟨189406526953303461408608513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505084071875475897089622701 189406526953303461408608513)
          ·
            refine ⟨142054895214977596056456385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189406526953303461408608513 142054895214977596056456385)
            ·
              refine ⟨106541171411233197042342289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142054895214977596056456385 106541171411233197042342289)
              ·
                refine ⟨79905878558424897781756717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106541171411233197042342289 79905878558424897781756717)
                ·
                  refine ⟨29964704459409336668158769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79905878558424897781756717 29964704459409336668158769)
                  ·
                    refine ⟨22473528344557002501119077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29964704459409336668158769 22473528344557002501119077)
                    ·
                      refine ⟨4213786564604437968959827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22473528344557002501119077 4213786564604437968959827)
                      ·
                        rfl

theorem cell23_8206320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_8206320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206320 prefixEnd_8206320 := by exact prefixLift 8206320
  have htrace : WordTrace (prefixWord ++ tailWord_8206320) baseStart_8206320 baseEnd_8206320 := by
    simpa [prefixWord, tailWord_8206320, baseEnd_8206320] using wordTrace_append hprefix tailTrace_8206320
  have hstable : (prefixWord ++ tailWord_8206320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206320).length < 2 ^ (prefixWord ++ tailWord_8206320).sum := by decide
  have hdescent : baseEnd_8206320 < baseStart_8206320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206334 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_8206334 : Nat := 118140960795 + 8206334 * 2 ^ 59
def prefixEnd_8206334 : Nat := 4983230072969 + 3 ^ 40 * 8206334 * 2
def baseEnd_8206334 : Nat := 1404597917777866971394921

theorem tailTrace_8206334 : CollatzResearch.WordTrace tailWord_8206334 prefixEnd_8206334 1404597917777866971394921 := by
  unfold tailWord_8206334
  simp only [CollatzResearch.WordTrace]
  refine ⟨37413698781482615388848257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199539726834573948740524037 37413698781482615388848257)
  ·
    refine ⟨28060274086111961541636193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37413698781482615388848257 28060274086111961541636193)
    ·
      refine ⟨21045205564583971156227145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28060274086111961541636193 21045205564583971156227145)
      ·
        refine ⟨15783904173437978367170359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21045205564583971156227145 15783904173437978367170359)
        ·
          refine ⟨23675856260156967550755539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15783904173437978367170359 23675856260156967550755539)
          ·
            refine ⟨35513784390235451326133309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23675856260156967550755539 35513784390235451326133309)
            ·
              refine ⟨13317669146338294247299991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35513784390235451326133309 13317669146338294247299991)
              ·
                refine ⟨19976503719507441370949987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13317669146338294247299991 19976503719507441370949987)
                ·
                  refine ⟨29964755579261162056424981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19976503719507441370949987 29964755579261162056424981)
                  ·
                    refine ⟨1404597917777866971394921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29964755579261162056424981 1404597917777866971394921)
                    ·
                      rfl

theorem cell23_8206334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_8206334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206334 prefixEnd_8206334 := by exact prefixLift 8206334
  have htrace : WordTrace (prefixWord ++ tailWord_8206334) baseStart_8206334 baseEnd_8206334 := by
    simpa [prefixWord, tailWord_8206334, baseEnd_8206334] using wordTrace_append hprefix tailTrace_8206334
  have hstable : (prefixWord ++ tailWord_8206334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206334).length < 2 ^ (prefixWord ++ tailWord_8206334).sum := by decide
  have hdescent : baseEnd_8206334 < baseStart_8206334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206344 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_8206344 : Nat := 118140960795 + 8206344 * 2 ^ 59
def prefixEnd_8206344 : Nat := 4983230072969 + 3 ^ 40 * 8206344 * 2
def baseEnd_8206344 : Nat := 4213798888140145875059717

theorem tailTrace_8206344 : CollatzResearch.WordTrace tailWord_8206344 prefixEnd_8206344 4213798888140145875059717 := by
  unfold tailWord_8206344
  simp only [CollatzResearch.WordTrace]
  refine ⟨149654977490912347409325043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199539969987883129879100057 149654977490912347409325043)
  ·
    refine ⟨224482466236368521113987565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149654977490912347409325043 224482466236368521113987565)
    ·
      refine ⟨84180924838638195417745337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224482466236368521113987565 84180924838638195417745337)
      ·
        refine ⟨63135693628978646563309003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84180924838638195417745337 63135693628978646563309003)
        ·
          refine ⟨94703540443467969844963505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63135693628978646563309003 94703540443467969844963505)
          ·
            refine ⟨71027655332600977383722629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94703540443467969844963505 71027655332600977383722629)
            ·
              refine ⟨13317685374862683259447993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71027655332600977383722629 13317685374862683259447993)
              ·
                refine ⟨9988264031147012444585995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13317685374862683259447993 9988264031147012444585995)
                ·
                  refine ⟨14982396046720518666878993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9988264031147012444585995 14982396046720518666878993)
                  ·
                    refine ⟨11236797035040389000159245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14982396046720518666878993 11236797035040389000159245)
                    ·
                      refine ⟨4213798888140145875059717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236797035040389000159245 4213798888140145875059717)
                      ·
                        rfl

theorem cell23_8206344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_8206344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206344 prefixEnd_8206344 := by exact prefixLift 8206344
  have htrace : WordTrace (prefixWord ++ tailWord_8206344) baseStart_8206344 baseEnd_8206344 := by
    simpa [prefixWord, tailWord_8206344, baseEnd_8206344] using wordTrace_append hprefix tailTrace_8206344
  have hstable : (prefixWord ++ tailWord_8206344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206344).length < 2 ^ (prefixWord ++ tailWord_8206344).sum := by decide
  have hdescent : baseEnd_8206344 < baseStart_8206344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206375 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_8206375 : Nat := 118140960795 + 8206375 * 2 ^ 59
def prefixEnd_8206375 : Nat := 4983230072969 + 3 ^ 40 * 8206375 * 2
def baseEnd_8206375 : Nat := 4213814806040435253772075

theorem tailTrace_8206375 : CollatzResearch.WordTrace tailWord_8206375 prefixEnd_8206375 4213814806040435253772075 := by
  unfold tailWord_8206375
  simp only [CollatzResearch.WordTrace]
  refine ⟨299311085644712387113028579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199540723763141591408685719 299311085644712387113028579)
  ·
    refine ⟨448966628467068580669542869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299311085644712387113028579 448966628467068580669542869)
    ·
      refine ⟨10522655354696919859442411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 448966628467068580669542869 10522655354696919859442411)
      ·
        refine ⟨15783983032045379789163617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10522655354696919859442411 15783983032045379789163617)
        ·
          refine ⟨11837987274034034841872713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15783983032045379789163617 11837987274034034841872713)
          ·
            refine ⟨8878490455525526131404535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11837987274034034841872713 8878490455525526131404535)
            ·
              refine ⟨13317735683288289197106803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878490455525526131404535 13317735683288289197106803)
              ·
                refine ⟨19976603524932433795660205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13317735683288289197106803 19976603524932433795660205)
                ·
                  refine ⟨7491226321849662673372577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19976603524932433795660205 7491226321849662673372577)
                  ·
                    refine ⟨5618419741387247005029433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7491226321849662673372577 5618419741387247005029433)
                    ·
                      refine ⟨4213814806040435253772075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618419741387247005029433 4213814806040435253772075)
                      ·
                        rfl

theorem cell23_8206375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_8206375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206375 prefixEnd_8206375 := by exact prefixLift 8206375
  have htrace : WordTrace (prefixWord ++ tailWord_8206375) baseStart_8206375 baseEnd_8206375 := by
    simpa [prefixWord, tailWord_8206375, baseEnd_8206375] using wordTrace_append hprefix tailTrace_8206375
  have hstable : (prefixWord ++ tailWord_8206375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206375).length < 2 ^ (prefixWord ++ tailWord_8206375).sum := by decide
  have hdescent : baseEnd_8206375 < baseStart_8206375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206391 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 2, 1, 3]
def baseStart_8206391 : Nat := 118140960795 + 8206391 * 2 ^ 59
def prefixEnd_8206391 : Nat := 4983230072969 + 3 ^ 40 * 8206391 * 2
def baseEnd_8206391 : Nat := 4213823021730907191172001

theorem tailTrace_8206391 : CollatzResearch.WordTrace tailWord_8206391 prefixEnd_8206391 4213823021730907191172001 := by
  unfold tailWord_8206391
  simp only [CollatzResearch.WordTrace]
  refine ⟨299311669212654421845611027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199541112808436281230407351 299311669212654421845611027)
  ·
    refine ⟨448967503818981632768416541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299311669212654421845611027 448967503818981632768416541)
    ·
      refine ⟨168362813932118112288156203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448967503818981632768416541 168362813932118112288156203)
      ·
        refine ⟨252544220898177168432234305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168362813932118112288156203 252544220898177168432234305)
        ·
          refine ⟨189408165673632876324175729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252544220898177168432234305 189408165673632876324175729)
          ·
            refine ⟨142056124255224657243131797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189408165673632876324175729 142056124255224657243131797)
            ·
              refine ⟨6658880824463655808271803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142056124255224657243131797 6658880824463655808271803)
              ·
                refine ⟨9988321236695483712407705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658880824463655808271803 9988321236695483712407705)
                ·
                  refine ⟨7491240927521612784305779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9988321236695483712407705 7491240927521612784305779)
                  ·
                    refine ⟨11236861391282419176458669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7491240927521612784305779 11236861391282419176458669)
                    ·
                      refine ⟨4213823021730907191172001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236861391282419176458669 4213823021730907191172001)
                      ·
                        rfl

theorem cell23_8206391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_8206391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206391 prefixEnd_8206391 := by exact prefixLift 8206391
  have htrace : WordTrace (prefixWord ++ tailWord_8206391) baseStart_8206391 baseEnd_8206391 := by
    simpa [prefixWord, tailWord_8206391, baseEnd_8206391] using wordTrace_append hprefix tailTrace_8206391
  have hstable : (prefixWord ++ tailWord_8206391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206391).length < 2 ^ (prefixWord ++ tailWord_8206391).sum := by decide
  have hdescent : baseEnd_8206391 < baseStart_8206391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206401 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_8206401 : Nat := 118140960795 + 8206401 * 2 ^ 59
def prefixEnd_8206401 : Nat := 4983230072969 + 3 ^ 40 * 8206401 * 2
def baseEnd_8206401 : Nat := 4213828156537452152046955

theorem tailTrace_8206401 : CollatzResearch.WordTrace tailWord_8206401 prefixEnd_8206401 4213828156537452152046955 := by
  unfold tailWord_8206401
  simp only [CollatzResearch.WordTrace]
  refine ⟨299312033942618193553475057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199541355961745462368983371 299312033942618193553475057)
  ·
    refine ⟨224484025456963645165106293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299312033942618193553475057 224484025456963645165106293)
    ·
      refine ⟨21045377386590341734228715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224484025456963645165106293 21045377386590341734228715)
      ·
        refine ⟨31568066079885512601343073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21045377386590341734228715 31568066079885512601343073)
        ·
          refine ⟨23676049559914134451007305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31568066079885512601343073 23676049559914134451007305)
          ·
            refine ⟨17757037169935600838255479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23676049559914134451007305 17757037169935600838255479)
            ·
              refine ⟨26635555754903401257383219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17757037169935600838255479 26635555754903401257383219)
              ·
                refine ⟨39953333632355101886074829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26635555754903401257383219 39953333632355101886074829)
                ·
                  refine ⟨14982500112133163207278061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39953333632355101886074829 14982500112133163207278061)
                  ·
                    refine ⟨5618437542049936202729273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14982500112133163207278061 5618437542049936202729273)
                    ·
                      refine ⟨4213828156537452152046955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618437542049936202729273 4213828156537452152046955)
                      ·
                        rfl

theorem cell23_8206401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_8206401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206401 prefixEnd_8206401 := by exact prefixLift 8206401
  have htrace : WordTrace (prefixWord ++ tailWord_8206401) baseStart_8206401 baseEnd_8206401 := by
    simpa [prefixWord, tailWord_8206401, baseEnd_8206401] using wordTrace_append hprefix tailTrace_8206401
  have hstable : (prefixWord ++ tailWord_8206401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206401).length < 2 ^ (prefixWord ++ tailWord_8206401).sum := by decide
  have hdescent : baseEnd_8206401 < baseStart_8206401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206414 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_8206414 : Nat := 118140960795 + 8206414 * 2 ^ 59
def prefixEnd_8206414 : Nat := 4983230072969 + 3 ^ 40 * 8206414 * 2
def baseEnd_8206414 : Nat := 4213834831785960601184395

theorem tailTrace_8206414 : CollatzResearch.WordTrace tailWord_8206414 prefixEnd_8206414 4213834831785960601184395 := by
  unfold tailWord_8206414
  simp only [CollatzResearch.WordTrace]
  refine ⟨37414063511446387096712287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199541672061047397849132197 37414063511446387096712287)
  ·
    refine ⟨56121095267169580645068431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37414063511446387096712287 56121095267169580645068431)
    ·
      refine ⟨84181642900754370967602647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56121095267169580645068431 84181642900754370967602647)
      ·
        refine ⟨126272464351131556451403971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84181642900754370967602647 126272464351131556451403971)
        ·
          refine ⟨189408696526697334677105957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126272464351131556451403971 189408696526697334677105957)
          ·
            refine ⟨35514130598755750251957367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189408696526697334677105957 35514130598755750251957367)
            ·
              refine ⟨53271195898133625377936051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35514130598755750251957367 53271195898133625377936051)
              ·
                refine ⟨79906793847200438066904077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53271195898133625377936051 79906793847200438066904077)
                ·
                  refine ⟨29965047692700164275089029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79906793847200438066904077 29965047692700164275089029)
                  ·
                    refine ⟨5618446442381280801579193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29965047692700164275089029 5618446442381280801579193)
                    ·
                      refine ⟨4213834831785960601184395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618446442381280801579193 4213834831785960601184395)
                      ·
                        rfl

theorem cell23_8206414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_8206414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206414 prefixEnd_8206414 := by exact prefixLift 8206414
  have htrace : WordTrace (prefixWord ++ tailWord_8206414) baseStart_8206414 baseEnd_8206414 := by
    simpa [prefixWord, tailWord_8206414, baseEnd_8206414] using wordTrace_append hprefix tailTrace_8206414
  have hstable : (prefixWord ++ tailWord_8206414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206414).length < 2 ^ (prefixWord ++ tailWord_8206414).sum := by decide
  have hdescent : baseEnd_8206414 < baseStart_8206414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206447 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 3]
def baseStart_8206447 : Nat := 118140960795 + 8206447 * 2 ^ 59
def prefixEnd_8206447 : Nat := 4983230072969 + 3 ^ 40 * 8206447 * 2
def baseEnd_8206447 : Nat := 4213851776647558972071743

theorem tailTrace_8206447 : CollatzResearch.WordTrace tailWord_8206447 prefixEnd_8206447 4213851776647558972071743 := by
  unfold tailWord_8206447
  simp only [CollatzResearch.WordTrace]
  refine ⟨299313711700451543409649595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199542474466967695606433063 299313711700451543409649595)
  ·
    refine ⟨448970567550677315114474393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299313711700451543409649595 448970567550677315114474393)
    ·
      refine ⟨336727925663007986335855795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448970567550677315114474393 336727925663007986335855795)
      ·
        refine ⟨505091888494511979503783693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336727925663007986335855795 505091888494511979503783693)
        ·
          refine ⟨189409458185441992313918885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505091888494511979503783693 189409458185441992313918885)
          ·
            refine ⟨35514273409770373558859791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189409458185441992313918885 35514273409770373558859791)
            ·
              refine ⟨53271410114655560338289687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35514273409770373558859791 53271410114655560338289687)
              ·
                refine ⟨79907115171983340507434531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53271410114655560338289687 79907115171983340507434531)
                ·
                  refine ⟨119860672757975010761151797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79907115171983340507434531 119860672757975010761151797)
                  ·
                    refine ⟨11236938071060157258857981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119860672757975010761151797 11236938071060157258857981)
                    ·
                      refine ⟨4213851776647558972071743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11236938071060157258857981 4213851776647558972071743)
                      ·
                        rfl

theorem cell23_8206447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_8206447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206447 prefixEnd_8206447 := by exact prefixLift 8206447
  have htrace : WordTrace (prefixWord ++ tailWord_8206447) baseStart_8206447 baseEnd_8206447 := by
    simpa [prefixWord, tailWord_8206447, baseEnd_8206447] using wordTrace_append hprefix tailTrace_8206447
  have hstable : (prefixWord ++ tailWord_8206447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206447).length < 2 ^ (prefixWord ++ tailWord_8206447).sum := by decide
  have hdescent : baseEnd_8206447 < baseStart_8206447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206454 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_8206454 : Nat := 118140960795 + 8206454 * 2 ^ 59
def prefixEnd_8206454 : Nat := 4983230072969 + 3 ^ 40 * 8206454 * 2
def baseEnd_8206454 : Nat := 468206152334682271631579

theorem tailTrace_8206454 : CollatzResearch.WordTrace tailWord_8206454 prefixEnd_8206454 468206152334682271631579 := by
  unfold tailWord_8206454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707122938214136475322151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199542644674284122403436277 18707122938214136475322151)
  ·
    refine ⟨28060684407321204712983227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18707122938214136475322151 28060684407321204712983227)
    ·
      refine ⟨42091026610981807069474841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28060684407321204712983227 42091026610981807069474841)
      ·
        refine ⟨31568269958236355302106131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42091026610981807069474841 31568269958236355302106131)
        ·
          refine ⟨47352404937354532953159197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31568269958236355302106131 47352404937354532953159197)
          ·
            refine ⟨17757151851507949857434699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47352404937354532953159197 17757151851507949857434699)
            ·
              refine ⟨26635727777261924786152049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17757151851507949857434699 26635727777261924786152049)
              ·
                refine ⟨19976795832946443589614037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26635727777261924786152049 19976795832946443589614037)
                ·
                  refine ⟨468206152334682271631579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19976795832946443589614037 468206152334682271631579)
                  ·
                    rfl

theorem cell23_8206454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_8206454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206454 prefixEnd_8206454 := by exact prefixLift 8206454
  have htrace : WordTrace (prefixWord ++ tailWord_8206454) baseStart_8206454 baseEnd_8206454 := by
    simpa [prefixWord, tailWord_8206454, baseEnd_8206454] using wordTrace_append hprefix tailTrace_8206454
  have hstable : (prefixWord ++ tailWord_8206454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206454).length < 2 ^ (prefixWord ++ tailWord_8206454).sum := by decide
  have hdescent : baseEnd_8206454 < baseStart_8206454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206467 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 1, 7]
def baseStart_8206467 : Nat := 118140960795 + 8206467 * 2 ^ 59
def prefixEnd_8206467 : Nat := 4983230072969 + 3 ^ 40 * 8206467 * 2
def baseEnd_8206467 : Nat := 1404620682086882964607217

theorem tailTrace_8206467 : CollatzResearch.WordTrace tailWord_8206467 prefixEnd_8206467 1404620682086882964607217 := by
  unfold tailWord_8206467
  simp only [CollatzResearch.WordTrace]
  refine ⟨299314441160379086825377655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199542960773586057883585103 299314441160379086825377655)
  ·
    refine ⟨448971661740568630238066483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299314441160379086825377655 448971661740568630238066483)
    ·
      refine ⟨673457492610852945357099725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448971661740568630238066483 673457492610852945357099725)
      ·
        refine ⟨252546559729069854508912397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673457492610852945357099725 252546559729069854508912397)
        ·
          refine ⟨94704959898401195440842149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252546559729069854508912397 94704959898401195440842149)
          ·
            refine ⟨17757179980950224145157903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94704959898401195440842149 17757179980950224145157903)
            ·
              refine ⟨26635769971425336217736855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17757179980950224145157903 26635769971425336217736855)
              ·
                refine ⟨39953654957138004326605283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26635769971425336217736855 39953654957138004326605283)
                ·
                  refine ⟨59930482435707006489907925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39953654957138004326605283 59930482435707006489907925)
                  ·
                    refine ⟨1404620682086882964607217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59930482435707006489907925 1404620682086882964607217)
                    ·
                      rfl

theorem cell23_8206467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 7].length) (baseStart_8206467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206467 prefixEnd_8206467 := by exact prefixLift 8206467
  have htrace : WordTrace (prefixWord ++ tailWord_8206467) baseStart_8206467 baseEnd_8206467 := by
    simpa [prefixWord, tailWord_8206467, baseEnd_8206467] using wordTrace_append hprefix tailTrace_8206467
  have hstable : (prefixWord ++ tailWord_8206467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206467).length < 2 ^ (prefixWord ++ tailWord_8206467).sum := by decide
  have hdescent : baseEnd_8206467 < baseStart_8206467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206514 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_8206514 : Nat := 118140960795 + 8206514 * 2 ^ 59
def prefixEnd_8206514 : Nat := 4983230072969 + 3 ^ 40 * 8206514 * 2
def baseEnd_8206514 : Nat := 1404628726617136736644645

theorem tailTrace_8206514 : CollatzResearch.WordTrace tailWord_8206514 prefixEnd_8206514 1404628726617136736644645 := by
  unfold tailWord_8206514
  simp only [CollatzResearch.WordTrace]
  refine ⟨74829038847802203463084649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199544103594139209234892397 74829038847802203463084649)
  ·
    refine ⟨56121779135851652597313487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74829038847802203463084649 56121779135851652597313487)
    ·
      refine ⟨84182668703777478895970231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56121779135851652597313487 84182668703777478895970231)
      ·
        refine ⟨126274003055666218343955347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84182668703777478895970231 126274003055666218343955347)
        ·
          refine ⟨189411004583499327515933021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126274003055666218343955347 189411004583499327515933021)
          ·
            refine ⟨71029126718812247818474883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189411004583499327515933021 71029126718812247818474883)
            ·
              refine ⟨106543690078218371727712325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71029126718812247818474883 106543690078218371727712325)
              ·
                refine ⟨19976941889665944698946061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106543690078218371727712325 19976941889665944698946061)
                ·
                  refine ⟨7491353208624729262104773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19976941889665944698946061 7491353208624729262104773)
                  ·
                    refine ⟨1404628726617136736644645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7491353208624729262104773 1404628726617136736644645)
                    ·
                      rfl

theorem cell23_8206514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_8206514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206514 prefixEnd_8206514 := by exact prefixLift 8206514
  have htrace : WordTrace (prefixWord ++ tailWord_8206514) baseStart_8206514 baseEnd_8206514 := by
    simpa [prefixWord, tailWord_8206514, baseEnd_8206514] using wordTrace_append hprefix tailTrace_8206514
  have hstable : (prefixWord ++ tailWord_8206514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206514).length < 2 ^ (prefixWord ++ tailWord_8206514).sum := by decide
  have hdescent : baseEnd_8206514 < baseStart_8206514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206591 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 1, 5]
def baseStart_8206591 : Nat := 118140960795 + 8206591 * 2 ^ 59
def prefixEnd_8206591 : Nat := 4983230072969 + 3 ^ 40 * 8206591 * 2
def baseEnd_8206591 : Nat := 1404641905953935469557027

theorem tailTrace_8206591 : CollatzResearch.WordTrace tailWord_8206591 prefixEnd_8206591 1404641905953935469557027 := by
  unfold tailWord_8206591
  simp only [CollatzResearch.WordTrace]
  refine ⟨299318963811929856002891627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199545975874619904001927751 299318963811929856002891627)
  ·
    refine ⟨448978445717894784004337441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299318963811929856002891627 448978445717894784004337441)
    ·
      refine ⟨336733834288421088003253081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448978445717894784004337441 336733834288421088003253081)
      ·
        refine ⟨252550375716315816002439811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336733834288421088003253081 252550375716315816002439811)
        ·
          refine ⟨378825563574473724003659717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252550375716315816002439811 378825563574473724003659717)
          ·
            refine ⟨71029793170213823250686197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378825563574473724003659717 71029793170213823250686197)
            ·
              refine ⟨6659043109707545929751831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71029793170213823250686197 6659043109707545929751831)
              ·
                refine ⟨9988564664561318894627747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659043109707545929751831 9988564664561318894627747)
                ·
                  refine ⟨14982846996841978341941621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9988564664561318894627747 14982846996841978341941621)
                  ·
                    refine ⟨1404641905953935469557027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14982846996841978341941621 1404641905953935469557027)
                    ·
                      rfl

theorem cell23_8206591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 5].length) (baseStart_8206591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206591 prefixEnd_8206591 := by exact prefixLift 8206591
  have htrace : WordTrace (prefixWord ++ tailWord_8206591) baseStart_8206591 baseEnd_8206591 := by
    simpa [prefixWord, tailWord_8206591, baseEnd_8206591] using wordTrace_append hprefix tailTrace_8206591
  have hstable : (prefixWord ++ tailWord_8206591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206591).length < 2 ^ (prefixWord ++ tailWord_8206591).sum := by decide
  have hdescent : baseEnd_8206591 < baseStart_8206591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206599 : List Nat := [1, 1, 4, 5, 2, 1, 2, 2, 1, 4]
def baseStart_8206599 : Nat := 118140960795 + 8206599 * 2 ^ 59
def prefixEnd_8206599 : Nat := 4983230072969 + 3 ^ 40 * 8206599 * 2
def baseEnd_8206599 : Nat := 1404643275235680792457015

theorem tailTrace_8206599 : CollatzResearch.WordTrace tailWord_8206599 prefixEnd_8206599 1404643275235680792457015 := by
  unfold tailWord_8206599
  simp only [CollatzResearch.WordTrace]
  refine ⟨299319255595900873369182851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199546170397267248912788567 299319255595900873369182851)
  ·
    refine ⟨448978883393851310053774277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299319255595900873369182851 448978883393851310053774277)
    ·
      refine ⟨84183540636347120635082677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448978883393851310053774277 84183540636347120635082677)
      ·
        refine ⟨7892206934657542559539001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84183540636347120635082677 7892206934657542559539001)
        ·
          refine ⟨5919155200993156919654251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7892206934657542559539001 5919155200993156919654251)
          ·
            refine ⟨8878732801489735379481377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919155200993156919654251 8878732801489735379481377)
            ·
              refine ⟨6659049601117301534611033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8878732801489735379481377 6659049601117301534611033)
              ·
                refine ⟨4994287200837976150958275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659049601117301534611033 4994287200837976150958275)
                ·
                  refine ⟨7491430801256964226437413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994287200837976150958275 7491430801256964226437413)
                  ·
                    refine ⟨1404643275235680792457015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7491430801256964226437413 1404643275235680792457015)
                    ·
                      rfl

theorem cell23_8206599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_8206599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206599 prefixEnd_8206599 := by exact prefixLift 8206599
  have htrace : WordTrace (prefixWord ++ tailWord_8206599) baseStart_8206599 baseEnd_8206599 := by
    simpa [prefixWord, tailWord_8206599, baseEnd_8206599] using wordTrace_append hprefix tailTrace_8206599
  have hstable : (prefixWord ++ tailWord_8206599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206599).length < 2 ^ (prefixWord ++ tailWord_8206599).sum := by decide
  have hdescent : baseEnd_8206599 < baseStart_8206599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206607 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_8206607 : Nat := 118140960795 + 8206607 * 2 ^ 59
def prefixEnd_8206607 : Nat := 4983230072969 + 3 ^ 40 * 8206607 * 2
def baseEnd_8206607 : Nat := 4213933933552278346071007

theorem tailTrace_8206607 : CollatzResearch.WordTrace tailWord_8206607 prefixEnd_8206607 4213933933552278346071007 := by
  unfold tailWord_8206607
  simp only [CollatzResearch.WordTrace]
  refine ⟨299319547379871890735474075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199546364919914593823649383 299319547379871890735474075)
  ·
    refine ⟨448979321069807836103211113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299319547379871890735474075 448979321069807836103211113)
    ·
      refine ⟨336734490802355877077408335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448979321069807836103211113 336734490802355877077408335)
      ·
        refine ⟨505101736203533815616112503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336734490802355877077408335 505101736203533815616112503)
        ·
          refine ⟨757652604305300723424168755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505101736203533815616112503 757652604305300723424168755)
          ·
            refine ⟨1136478906457951085136253133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757652604305300723424168755 1136478906457951085136253133)
            ·
              refine ⟨426179589921731656926094925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136478906457951085136253133 426179589921731656926094925)
              ·
                refine ⟨159817346220649371347285597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426179589921731656926094925 159817346220649371347285597)
                ·
                  refine ⟨59931504832743514255232099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159817346220649371347285597 59931504832743514255232099)
                  ·
                    refine ⟨89897257249115271382848149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59931504832743514255232099 89897257249115271382848149)
                    ·
                      refine ⟨4213933933552278346071007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89897257249115271382848149 4213933933552278346071007)
                      ·
                        rfl

theorem cell23_8206607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_8206607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206607 prefixEnd_8206607 := by exact prefixLift 8206607
  have htrace : WordTrace (prefixWord ++ tailWord_8206607) baseStart_8206607 baseEnd_8206607 := by
    simpa [prefixWord, tailWord_8206607, baseEnd_8206607] using wordTrace_append hprefix tailTrace_8206607
  have hstable : (prefixWord ++ tailWord_8206607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206607).length < 2 ^ (prefixWord ++ tailWord_8206607).sum := by decide
  have hdescent : baseEnd_8206607 < baseStart_8206607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206611 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 7, 2, 2]
def baseStart_8206611 : Nat := 118140960795 + 8206611 * 2 ^ 59
def prefixEnd_8206611 : Nat := 4983230072969 + 3 ^ 40 * 8206611 * 2
def baseEnd_8206611 : Nat := 4213935987474896330420989

theorem tailTrace_8206611 : CollatzResearch.WordTrace tailWord_8206611 prefixEnd_8206611 4213935987474896330420989 := by
  unfold tailWord_8206611
  simp only [CollatzResearch.WordTrace]
  refine ⟨299319693271857399418619687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199546462181238266279079791 299319693271857399418619687)
  ·
    refine ⟨448979539907786099127929531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299319693271857399418619687 448979539907786099127929531)
    ·
      refine ⟨673469309861679148691894297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448979539907786099127929531 673469309861679148691894297)
      ·
        refine ⟨505101982396259361518920723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673469309861679148691894297 505101982396259361518920723)
        ·
          refine ⟨757652973594389042278381085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505101982396259361518920723 757652973594389042278381085)
          ·
            refine ⟨284119865097895890854392907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 757652973594389042278381085 284119865097895890854392907)
            ·
              refine ⟨426179797646843836281589361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284119865097895890854392907 426179797646843836281589361)
              ·
                refine ⟨319634848235132877211192021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426179797646843836281589361 319634848235132877211192021)
                ·
                  refine ⟨7491441755510926809637313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 319634848235132877211192021 7491441755510926809637313)
                  ·
                    refine ⟨5618581316633195107227985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7491441755510926809637313 5618581316633195107227985)
                    ·
                      refine ⟨4213935987474896330420989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618581316633195107227985 4213935987474896330420989)
                      ·
                        rfl

theorem cell23_8206611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 2, 2].length) (baseStart_8206611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206611 prefixEnd_8206611 := by exact prefixLift 8206611
  have htrace : WordTrace (prefixWord ++ tailWord_8206611) baseStart_8206611 baseEnd_8206611 := by
    simpa [prefixWord, tailWord_8206611, baseEnd_8206611] using wordTrace_append hprefix tailTrace_8206611
  have hstable : (prefixWord ++ tailWord_8206611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206611).length < 2 ^ (prefixWord ++ tailWord_8206611).sum := by decide
  have hdescent : baseEnd_8206611 < baseStart_8206611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206628 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_8206628 : Nat := 118140960795 + 8206628 * 2 ^ 59
def prefixEnd_8206628 : Nat := 4983230072969 + 3 ^ 40 * 8206628 * 2
def baseEnd_8206628 : Nat := 4213944716646022763908411

theorem tailTrace_8206628 : CollatzResearch.WordTrace tailWord_8206628 prefixEnd_8206628 4213944716646022763908411 := by
  unfold tailWord_8206628
  simp only [CollatzResearch.WordTrace]
  refine ⟨149660156656397905660994269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199546875541863874214659025 149660156656397905660994269)
  ·
    refine ⟨56122558746149214622872851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149660156656397905660994269 56122558746149214622872851)
    ·
      refine ⟨84183838119223821934309277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56122558746149214622872851 84183838119223821934309277)
      ·
        refine ⟨31568939294708933225365979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84183838119223821934309277 31568939294708933225365979)
        ·
          refine ⟨47353408942063399838048969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31568939294708933225365979 47353408942063399838048969)
          ·
            refine ⟨35515056706547549878536727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47353408942063399838048969 35515056706547549878536727)
            ·
              refine ⟨53272585059821324817805091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35515056706547549878536727 53272585059821324817805091)
              ·
                refine ⟨79908877589731987226707637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53272585059821324817805091 79908877589731987226707637)
                ·
                  refine ⟨7491457274037373802503841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79908877589731987226707637 7491457274037373802503841)
                  ·
                    refine ⟨5618592955528030351877881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7491457274037373802503841 5618592955528030351877881)
                    ·
                      refine ⟨4213944716646022763908411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618592955528030351877881 4213944716646022763908411)
                      ·
                        rfl

theorem cell23_8206628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_8206628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206628 prefixEnd_8206628 := by exact prefixLift 8206628
  have htrace : WordTrace (prefixWord ++ tailWord_8206628) baseStart_8206628 baseEnd_8206628 := by
    simpa [prefixWord, tailWord_8206628, baseEnd_8206628] using wordTrace_append hprefix tailTrace_8206628
  have hstable : (prefixWord ++ tailWord_8206628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206628).length < 2 ^ (prefixWord ++ tailWord_8206628).sum := by decide
  have hdescent : baseEnd_8206628 < baseStart_8206628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206632 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_8206632 : Nat := 118140960795 + 8206632 * 2 ^ 59
def prefixEnd_8206632 : Nat := 4983230072969 + 3 ^ 40 * 8206632 * 2
def baseEnd_8206632 : Nat := 4213946770568640748258393

theorem tailTrace_8206632 : CollatzResearch.WordTrace tailWord_8206632 prefixEnd_8206632 4213946770568640748258393 := by
  unfold tailWord_8206632
  simp only [CollatzResearch.WordTrace]
  refine ⟨149660229602390660002567075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199546972803187546670089433 149660229602390660002567075)
  ·
    refine ⟨224490344403585990003850613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149660229602390660002567075 224490344403585990003850613)
    ·
      refine ⟨21045969787836186562860995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224490344403585990003850613 21045969787836186562860995)
      ·
        refine ⟨31568954681754279844291493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21045969787836186562860995 31568954681754279844291493)
        ·
          refine ⟨5919179002828927470804655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31568954681754279844291493 5919179002828927470804655)
          ·
            refine ⟨8878768504243391206206983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919179002828927470804655 8878768504243391206206983)
            ·
              refine ⟨13318152756365086809310475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878768504243391206206983 13318152756365086809310475)
              ·
                refine ⟨19977229134547630213965713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13318152756365086809310475 19977229134547630213965713)
                ·
                  refine ⟨14982921850910722660474285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19977229134547630213965713 14982921850910722660474285)
                  ·
                    refine ⟨5618595694091520997677857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14982921850910722660474285 5618595694091520997677857)
                    ·
                      refine ⟨4213946770568640748258393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618595694091520997677857 4213946770568640748258393)
                      ·
                        rfl

theorem cell23_8206632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_8206632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206632 prefixEnd_8206632 := by exact prefixLift 8206632
  have htrace : WordTrace (prefixWord ++ tailWord_8206632) baseStart_8206632 baseEnd_8206632 := by
    simpa [prefixWord, tailWord_8206632, baseEnd_8206632] using wordTrace_append hprefix tailTrace_8206632
  have hstable : (prefixWord ++ tailWord_8206632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206632).length < 2 ^ (prefixWord ++ tailWord_8206632).sum := by decide
  have hdescent : baseEnd_8206632 < baseStart_8206632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206648 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 1, 2, 3]
def baseStart_8206648 : Nat := 118140960795 + 8206648 * 2 ^ 59
def prefixEnd_8206648 : Nat := 4983230072969 + 3 ^ 40 * 8206648 * 2
def baseEnd_8206648 : Nat := 4213954986259112685658319

theorem tailTrace_8206648 : CollatzResearch.WordTrace tailWord_8206648 prefixEnd_8206648 4213954986259112685658319 := by
  unfold tailWord_8206648
  simp only [CollatzResearch.WordTrace]
  refine ⟨149660521386361677368858299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199547361848482236491811065 149660521386361677368858299)
  ·
    refine ⟨224490782079542516053287449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149660521386361677368858299 224490782079542516053287449)
    ·
      refine ⟨168368086559656887039965587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224490782079542516053287449 168368086559656887039965587)
      ·
        refine ⟨252552129839485330559948381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168368086559656887039965587 252552129839485330559948381)
        ·
          refine ⟨94707048689806998959980643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252552129839485330559948381 94707048689806998959980643)
          ·
            refine ⟨142060573034710498439970965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94707048689806998959980643 142060573034710498439970965)
            ·
              refine ⟨6659089361002054614373639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142060573034710498439970965 6659089361002054614373639)
              ·
                refine ⟨9988634041503081921560459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659089361002054614373639 9988634041503081921560459)
                ·
                  refine ⟨14982951062254622882340689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9988634041503081921560459 14982951062254622882340689)
                  ·
                    refine ⟨11237213296690967161755517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14982951062254622882340689 11237213296690967161755517)
                    ·
                      refine ⟨4213954986259112685658319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11237213296690967161755517 4213954986259112685658319)
                      ·
                        rfl

theorem cell23_8206648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_8206648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206648 prefixEnd_8206648 := by exact prefixLift 8206648
  have htrace : WordTrace (prefixWord ++ tailWord_8206648) baseStart_8206648 baseEnd_8206648 := by
    simpa [prefixWord, tailWord_8206648, baseEnd_8206648] using wordTrace_append hprefix tailTrace_8206648
  have hstable : (prefixWord ++ tailWord_8206648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206648).length < 2 ^ (prefixWord ++ tailWord_8206648).sum := by decide
  have hdescent : baseEnd_8206648 < baseStart_8206648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206671 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 3, 3, 2]
def baseStart_8206671 : Nat := 118140960795 + 8206671 * 2 ^ 59
def prefixEnd_8206671 : Nat := 4983230072969 + 3 ^ 40 * 8206671 * 2
def baseEnd_8206671 : Nat := 4213966796314166095670713

theorem tailTrace_8206671 : CollatzResearch.WordTrace tailWord_8206671 prefixEnd_8206671 4213966796314166095670713 := by
  unfold tailWord_8206671
  simp only [CollatzResearch.WordTrace]
  refine ⟨299321881651640029665803867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199547921101093353110535911 299321881651640029665803867)
  ·
    refine ⟨448982822477460044498705801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299321881651640029665803867 448982822477460044498705801)
    ·
      refine ⟨336737116858095033374029351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448982822477460044498705801 336737116858095033374029351)
      ·
        refine ⟨505105675287142550061044027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336737116858095033374029351 505105675287142550061044027)
        ·
          refine ⟨757658512930713825091566041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505105675287142550061044027 757658512930713825091566041)
          ·
            refine ⟨568243884698035368818674531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757658512930713825091566041 568243884698035368818674531)
            ·
              refine ⟨852365827047053053228011797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568243884698035368818674531 852365827047053053228011797)
              ·
                refine ⟨39954648142830611870063053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 852365827047053053228011797 39954648142830611870063053)
                ·
                  refine ⟨14982993053561479451273645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39954648142830611870063053 14982993053561479451273645)
                  ·
                    refine ⟨5618622395085554794227617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14982993053561479451273645 5618622395085554794227617)
                    ·
                      refine ⟨4213966796314166095670713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618622395085554794227617 4213966796314166095670713)
                      ·
                        rfl

theorem cell23_8206671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 3, 2].length) (baseStart_8206671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206671 prefixEnd_8206671 := by exact prefixLift 8206671
  have htrace : WordTrace (prefixWord ++ tailWord_8206671) baseStart_8206671 baseEnd_8206671 := by
    simpa [prefixWord, tailWord_8206671, baseEnd_8206671] using wordTrace_append hprefix tailTrace_8206671
  have hstable : (prefixWord ++ tailWord_8206671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206671).length < 2 ^ (prefixWord ++ tailWord_8206671).sum := by decide
  have hdescent : baseEnd_8206671 < baseStart_8206671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206704 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_8206704 : Nat := 118140960795 + 8206704 * 2 ^ 59
def prefixEnd_8206704 : Nat := 4983230072969 + 3 ^ 40 * 8206704 * 2
def baseEnd_8206704 : Nat := 4213983741175764466558061

theorem tailTrace_8206704 : CollatzResearch.WordTrace tailWord_8206704 prefixEnd_8206704 4213983741175764466558061 := by
  unfold tailWord_8206704
  simp only [CollatzResearch.WordTrace]
  refine ⟨149661542630260238150877583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199548723507013650867836777 149661542630260238150877583)
  ·
    refine ⟨224492313945390357226316375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149661542630260238150877583 224492313945390357226316375)
    ·
      refine ⟨336738470918085535839474563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224492313945390357226316375 336738470918085535839474563)
      ·
        refine ⟨505107706377128303759211845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336738470918085535839474563 505107706377128303759211845)
        ·
          refine ⟨94707694945711556954852221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505107706377128303759211845 94707694945711556954852221)
          ·
            refine ⟨35515385604641833858069583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94707694945711556954852221 35515385604641833858069583)
            ·
              refine ⟨53273078406962750787104375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35515385604641833858069583 53273078406962750787104375)
              ·
                refine ⟨79909617610444126180656563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53273078406962750787104375 79909617610444126180656563)
                ·
                  refine ⟨119864426415666189270984845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79909617610444126180656563 119864426415666189270984845)
                  ·
                    refine ⟨44949159905874820976619317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119864426415666189270984845 44949159905874820976619317)
                    ·
                      refine ⟨4213983741175764466558061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44949159905874820976619317 4213983741175764466558061)
                      ·
                        rfl

theorem cell23_8206704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_8206704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206704 prefixEnd_8206704 := by exact prefixLift 8206704
  have htrace : WordTrace (prefixWord ++ tailWord_8206704) baseStart_8206704 baseEnd_8206704 := by
    simpa [prefixWord, tailWord_8206704, baseEnd_8206704] using wordTrace_append hprefix tailTrace_8206704
  have hstable : (prefixWord ++ tailWord_8206704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206704).length < 2 ^ (prefixWord ++ tailWord_8206704).sum := by decide
  have hdescent : baseEnd_8206704 < baseStart_8206704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206761 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 4, 5, 2]
def baseStart_8206761 : Nat := 118140960795 + 8206761 * 2 ^ 59
def prefixEnd_8206761 : Nat := 4983230072969 + 3 ^ 40 * 8206761 * 2
def baseEnd_8206761 : Nat := 4214013009573070743545299

theorem tailTrace_8206761 : CollatzResearch.WordTrace tailWord_8206761 prefixEnd_8206761 4214013009573070743545299 := by
  unfold tailWord_8206761
  simp only [CollatzResearch.WordTrace]
  refine ⟨299325164221313975036580137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199550109480875983357720091 299325164221313975036580137)
  ·
    refine ⟨224493873165985481277435103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299325164221313975036580137 224493873165985481277435103)
    ·
      refine ⟨336740809748978221916152655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224493873165985481277435103 336740809748978221916152655)
      ·
        refine ⟨505111214623467332874228983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336740809748978221916152655 505111214623467332874228983)
        ·
          refine ⟨757666821935200999311343475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505111214623467332874228983 757666821935200999311343475)
          ·
            refine ⟨1136500232902801498967015213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757666821935200999311343475 1136500232902801498967015213)
            ·
              refine ⟨426187587338550562112630705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136500232902801498967015213 426187587338550562112630705)
              ·
                refine ⟨319640690503912921584473029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426187587338550562112630705 319640690503912921584473029)
                ·
                  refine ⟨59932629469483672797088693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319640690503912921584473029 59932629469483672797088693)
                  ·
                    refine ⟨5618684012764094324727065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59932629469483672797088693 5618684012764094324727065)
                    ·
                      refine ⟨4214013009573070743545299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618684012764094324727065 4214013009573070743545299)
                      ·
                        rfl

theorem cell23_8206761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 5, 2].length) (baseStart_8206761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206761 prefixEnd_8206761 := by exact prefixLift 8206761
  have htrace : WordTrace (prefixWord ++ tailWord_8206761) baseStart_8206761 baseEnd_8206761 := by
    simpa [prefixWord, tailWord_8206761, baseEnd_8206761] using wordTrace_append hprefix tailTrace_8206761
  have hstable : (prefixWord ++ tailWord_8206761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206761).length < 2 ^ (prefixWord ++ tailWord_8206761).sum := by decide
  have hdescent : baseEnd_8206761 < baseStart_8206761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206775 : List Nat := [1, 1, 3, 1, 3, 5, 2, 2, 5]
def baseStart_8206775 : Nat := 118140960795 + 8206775 * 2 ^ 59
def prefixEnd_8206775 : Nat := 4983230072969 + 3 ^ 40 * 8206775 * 2
def baseEnd_8206775 : Nat := 468224466478025965418915

theorem tailTrace_8206775 : CollatzResearch.WordTrace tailWord_8206775 prefixEnd_8206775 468224466478025965418915 := by
  unfold tailWord_8206775
  simp only [CollatzResearch.WordTrace]
  refine ⟨299325674843263255427589779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199550449895508836951726519 299325674843263255427589779)
  ·
    refine ⟨448988512264894883141384669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299325674843263255427589779 448988512264894883141384669)
    ·
      refine ⟨168370692099335581178019251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448988512264894883141384669 168370692099335581178019251)
      ·
        refine ⟨252556038149003371767028877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168370692099335581178019251 252556038149003371767028877)
        ·
          refine ⟨94708514305876264412635829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252556038149003371767028877 94708514305876264412635829)
          ·
            refine ⟨8878923216175899788684609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94708514305876264412635829 8878923216175899788684609)
            ·
              refine ⟨6659192412131924841513457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8878923216175899788684609 6659192412131924841513457)
              ·
                refine ⟨4994394309098943631135093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659192412131924841513457 4994394309098943631135093)
                ·
                  refine ⟨468224466478025965418915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4994394309098943631135093 468224466478025965418915)
                  ·
                    rfl

theorem cell23_8206775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 5].length) (baseStart_8206775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206775 prefixEnd_8206775 := by exact prefixLift 8206775
  have htrace : WordTrace (prefixWord ++ tailWord_8206775) baseStart_8206775 baseEnd_8206775 := by
    simpa [prefixWord, tailWord_8206775, baseEnd_8206775] using wordTrace_append hprefix tailTrace_8206775
  have hstable : (prefixWord ++ tailWord_8206775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206775).length < 2 ^ (prefixWord ++ tailWord_8206775).sum := by decide
  have hdescent : baseEnd_8206775 < baseStart_8206775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206781 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_8206781 : Nat := 118140960795 + 8206781 * 2 ^ 59
def prefixEnd_8206781 : Nat := 4983230072969 + 3 ^ 40 * 8206781 * 2
def baseEnd_8206781 : Nat := 4214023279186160665295207

theorem tailTrace_8206781 : CollatzResearch.WordTrace tailWord_8206781 prefixEnd_8206781 4214023279186160665295207 := by
  unfold tailWord_8206781
  simp only [CollatzResearch.WordTrace]
  refine ⟨299325893681241518452308197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199550595787494345634872131 299325893681241518452308197)
  ·
    refine ⟨56123605065232784709807787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299325893681241518452308197 56123605065232784709807787)
    ·
      refine ⟨84185407597849177064711681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56123605065232784709807787 84185407597849177064711681)
      ·
        refine ⟨63139055698386882798533761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84185407597849177064711681 63139055698386882798533761)
        ·
          refine ⟨47354291773790162098900321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63139055698386882798533761 47354291773790162098900321)
          ·
            refine ⟨35515718830342621574175241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47354291773790162098900321 35515718830342621574175241)
            ·
              refine ⟨26636789122756966180631431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35515718830342621574175241 26636789122756966180631431)
              ·
                refine ⟨39955183684135449270947147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26636789122756966180631431 39955183684135449270947147)
                ·
                  refine ⟨59932775526203173906420721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39955183684135449270947147 59932775526203173906420721)
                  ·
                    refine ⟨44949581644652380429815541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59932775526203173906420721 44949581644652380429815541)
                    ·
                      refine ⟨4214023279186160665295207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44949581644652380429815541 4214023279186160665295207)
                      ·
                        rfl

theorem cell23_8206781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_8206781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206781 prefixEnd_8206781 := by exact prefixLift 8206781
  have htrace : WordTrace (prefixWord ++ tailWord_8206781) baseStart_8206781 baseEnd_8206781 := by
    simpa [prefixWord, tailWord_8206781, baseEnd_8206781] using wordTrace_append hprefix tailTrace_8206781
  have hstable : (prefixWord ++ tailWord_8206781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206781).length < 2 ^ (prefixWord ++ tailWord_8206781).sum := by decide
  have hdescent : baseEnd_8206781 < baseStart_8206781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206784 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 2, 8]
def baseStart_8206784 : Nat := 118140960795 + 8206784 * 2 ^ 59
def prefixEnd_8206784 : Nat := 4983230072969 + 3 ^ 40 * 8206784 * 2
def baseEnd_8206784 : Nat := 1404674939876041384519231

theorem tailTrace_8206784 : CollatzResearch.WordTrace tailWord_8206784 prefixEnd_8206784 1404674939876041384519231 := by
  unfold tailWord_8206784
  simp only [CollatzResearch.WordTrace]
  refine ⟨149663001550115324982333703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199550668733487099976444937 149663001550115324982333703)
  ·
    refine ⟨224494502325172987473500555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149663001550115324982333703 224494502325172987473500555)
    ·
      refine ⟨336741753487759481210250833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224494502325172987473500555 336741753487759481210250833)
      ·
        refine ⟨252556315115819610907688125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336741753487759481210250833 252556315115819610907688125)
        ·
          refine ⟨94708618168432354090383047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252556315115819610907688125 94708618168432354090383047)
          ·
            refine ⟨142062927252648531135574571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94708618168432354090383047 142062927252648531135574571)
            ·
              refine ⟨213094390878972796703361857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142062927252648531135574571 213094390878972796703361857)
              ·
                refine ⟨159820793159229597527521393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213094390878972796703361857 159820793159229597527521393)
                ·
                  refine ⟨119865594869422198145641045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159820793159229597527521393 119865594869422198145641045)
                  ·
                    refine ⟨1404674939876041384519231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119865594869422198145641045 1404674939876041384519231)
                    ·
                      rfl

theorem cell23_8206784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_8206784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206784 prefixEnd_8206784 := by exact prefixLift 8206784
  have htrace : WordTrace (prefixWord ++ tailWord_8206784) baseStart_8206784 baseEnd_8206784 := by
    simpa [prefixWord, tailWord_8206784, baseEnd_8206784] using wordTrace_append hprefix tailTrace_8206784
  have hstable : (prefixWord ++ tailWord_8206784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206784).length < 2 ^ (prefixWord ++ tailWord_8206784).sum := by decide
  have hdescent : baseEnd_8206784 < baseStart_8206784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206911 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_8206911 : Nat := 118140960795 + 8206911 * 2 ^ 59
def prefixEnd_8206911 : Nat := 4983230072969 + 3 ^ 40 * 8206911 * 2
def baseEnd_8206911 : Nat := 4214090031671245156669609

theorem tailTrace_8206911 : CollatzResearch.WordTrace tailWord_8206911 prefixEnd_8206911 4214090031671245156669609 := by
  unfold tailWord_8206911
  simp only [CollatzResearch.WordTrace]
  refine ⟨299330635170770550654540587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199553756780513700436360391 299330635170770550654540587)
  ·
    refine ⟨448995952756155825981810881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299330635170770550654540587 448995952756155825981810881)
    ·
      refine ⟨336746964567116869486358161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448995952756155825981810881 336746964567116869486358161)
      ·
        refine ⟨252560223425337652114768621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336746964567116869486358161 252560223425337652114768621)
        ·
          refine ⟨94710083784501619543038233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252560223425337652114768621 94710083784501619543038233)
          ·
            refine ⟨71032562838376214657278675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94710083784501619543038233 71032562838376214657278675)
            ·
              refine ⟨106548844257564321985918013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71032562838376214657278675 106548844257564321985918013)
              ·
                refine ⟨39955816596586620744719255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106548844257564321985918013 39955816596586620744719255)
                ·
                  refine ⟨59933724894879931117078883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39955816596586620744719255 59933724894879931117078883)
                  ·
                    refine ⟨89900587342319896675618325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59933724894879931117078883 89900587342319896675618325)
                    ·
                      refine ⟨4214090031671245156669609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89900587342319896675618325 4214090031671245156669609)
                      ·
                        rfl

theorem cell23_8206911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_8206911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206911 prefixEnd_8206911 := by exact prefixLift 8206911
  have htrace : WordTrace (prefixWord ++ tailWord_8206911) baseStart_8206911 baseEnd_8206911 := by
    simpa [prefixWord, tailWord_8206911, baseEnd_8206911] using wordTrace_append hprefix tailTrace_8206911
  have hstable : (prefixWord ++ tailWord_8206911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206911).length < 2 ^ (prefixWord ++ tailWord_8206911).sum := by decide
  have hdescent : baseEnd_8206911 < baseStart_8206911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206915 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 3, 2, 2]
def baseStart_8206915 : Nat := 118140960795 + 8206915 * 2 ^ 59
def prefixEnd_8206915 : Nat := 4983230072969 + 3 ^ 40 * 8206915 * 2
def baseEnd_8206915 : Nat := 4214092085593863141019591

theorem tailTrace_8206915 : CollatzResearch.WordTrace tailWord_8206915 prefixEnd_8206915 4214092085593863141019591 := by
  unfold tailWord_8206915
  simp only [CollatzResearch.WordTrace]
  refine ⟨299330781062756059337686199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199553854041837372891790799 299330781062756059337686199)
  ·
    refine ⟨448996171594134089006529299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299330781062756059337686199 448996171594134089006529299)
    ·
      refine ⟨673494257391201133509793949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448996171594134089006529299 673494257391201133509793949)
      ·
        refine ⟨252560346521700425066172731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673494257391201133509793949 252560346521700425066172731)
        ·
          refine ⟨378840519782550637599259097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252560346521700425066172731 378840519782550637599259097)
          ·
            refine ⟨284130389836912978199444323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378840519782550637599259097 284130389836912978199444323)
            ·
              refine ⟨426195584755369467299166485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284130389836912978199444323 426195584755369467299166485)
              ·
                refine ⟨19977918035407943779648429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 426195584755369467299166485 19977918035407943779648429)
                ·
                  refine ⟨7491719263277978917368161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19977918035407943779648429 7491719263277978917368161)
                  ·
                    refine ⟨5618789447458484188026121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7491719263277978917368161 5618789447458484188026121)
                    ·
                      refine ⟨4214092085593863141019591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618789447458484188026121 4214092085593863141019591)
                      ·
                        rfl

theorem cell23_8206915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_8206915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206915 prefixEnd_8206915 := by exact prefixLift 8206915
  have htrace : WordTrace (prefixWord ++ tailWord_8206915) baseStart_8206915 baseEnd_8206915 := by
    simpa [prefixWord, tailWord_8206915, baseEnd_8206915] using wordTrace_append hprefix tailTrace_8206915
  have hstable : (prefixWord ++ tailWord_8206915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206915).length < 2 ^ (prefixWord ++ tailWord_8206915).sum := by decide
  have hdescent : baseEnd_8206915 < baseStart_8206915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206925 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_8206925 : Nat := 118140960795 + 8206925 * 2 ^ 59
def prefixEnd_8206925 : Nat := 4983230072969 + 3 ^ 40 * 8206925 * 2
def baseEnd_8206925 : Nat := 1404699073466802700631515

theorem tailTrace_8206925 : CollatzResearch.WordTrace tailWord_8206925 prefixEnd_8206925 1404699073466802700631515 := by
  unfold tailWord_8206925
  simp only [CollatzResearch.WordTrace]
  refine ⟨299331145792719831045550229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199554097195146554030366819 299331145792719831045550229)
  ·
    refine ⟨14031147459033742080260167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 299331145792719831045550229 14031147459033742080260167)
    ·
      refine ⟨21046721188550613120390251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14031147459033742080260167 21046721188550613120390251)
      ·
        refine ⟨31570081782825919680585377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21046721188550613120390251 31570081782825919680585377)
        ·
          refine ⟨23677561337119439760439033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31570081782825919680585377 23677561337119439760439033)
          ·
            refine ⟨17758171002839579820329275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23677561337119439760439033 17758171002839579820329275)
            ·
              refine ⟨26637256504259369730493913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17758171002839579820329275 26637256504259369730493913)
              ·
                refine ⟨19977942378194527297870435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26637256504259369730493913 19977942378194527297870435)
                ·
                  refine ⟨29966913567291790946805653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19977942378194527297870435 29966913567291790946805653)
                  ·
                    refine ⟨1404699073466802700631515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29966913567291790946805653 1404699073466802700631515)
                    ·
                      rfl

theorem cell23_8206925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_8206925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206925 prefixEnd_8206925 := by exact prefixLift 8206925
  have htrace : WordTrace (prefixWord ++ tailWord_8206925) baseStart_8206925 baseEnd_8206925 := by
    simpa [prefixWord, tailWord_8206925, baseEnd_8206925] using wordTrace_append hprefix tailTrace_8206925
  have hstable : (prefixWord ++ tailWord_8206925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206925).length < 2 ^ (prefixWord ++ tailWord_8206925).sum := by decide
  have hdescent : baseEnd_8206925 < baseStart_8206925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206932 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_8206932 : Nat := 118140960795 + 8206932 * 2 ^ 59
def prefixEnd_8206932 : Nat := 4983230072969 + 3 ^ 40 * 8206932 * 2
def baseEnd_8206932 : Nat := 4214100814764989574507013

theorem tailTrace_8206932 : CollatzResearch.WordTrace tailWord_8206932 prefixEnd_8206932 4214100814764989574507013 := by
  unfold tailWord_8206932
  simp only [CollatzResearch.WordTrace]
  refine ⟨149665700551847235620527525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199554267402462980827370033 149665700551847235620527525)
  ·
    refine ⟨28062318853471356678848911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149665700551847235620527525 28062318853471356678848911)
    ·
      refine ⟨42093478280207035018273367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28062318853471356678848911 42093478280207035018273367)
      ·
        refine ⟨63140217420310552527410051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42093478280207035018273367 63140217420310552527410051)
        ·
          refine ⟨94710326130465828791115077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63140217420310552527410051 94710326130465828791115077)
          ·
            refine ⟨17758186149462342898334077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94710326130465828791115077 17758186149462342898334077)
            ·
              refine ⟨6659319806048378586875279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17758186149462342898334077 6659319806048378586875279)
              ·
                refine ⟨9988979709072567880312919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659319806048378586875279 9988979709072567880312919)
                ·
                  refine ⟨14983469563608851820469379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9988979709072567880312919 14983469563608851820469379)
                  ·
                    refine ⟨22475204345413277730704069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14983469563608851820469379 22475204345413277730704069)
                    ·
                      refine ⟨4214100814764989574507013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22475204345413277730704069 4214100814764989574507013)
                      ·
                        rfl

theorem cell23_8206932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_8206932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206932 prefixEnd_8206932 := by exact prefixLift 8206932
  have htrace : WordTrace (prefixWord ++ tailWord_8206932) baseStart_8206932 baseEnd_8206932 := by
    simpa [prefixWord, tailWord_8206932, baseEnd_8206932] using wordTrace_append hprefix tailTrace_8206932
  have hstable : (prefixWord ++ tailWord_8206932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206932).length < 2 ^ (prefixWord ++ tailWord_8206932).sum := by decide
  have hdescent : baseEnd_8206932 < baseStart_8206932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206948 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_8206948 : Nat := 118140960795 + 8206948 * 2 ^ 59
def prefixEnd_8206948 : Nat := 4983230072969 + 3 ^ 40 * 8206948 * 2
def baseEnd_8206948 : Nat := 4214109030455461511906939

theorem tailTrace_8206948 : CollatzResearch.WordTrace tailWord_8206948 prefixEnd_8206948 4214109030455461511906939 := by
  unfold tailWord_8206948
  simp only [CollatzResearch.WordTrace]
  refine ⟨149665992335818252986818749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199554656447757670649091665 149665992335818252986818749)
  ·
    refine ⟨56124747125931844870057031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149665992335818252986818749 56124747125931844870057031)
    ·
      refine ⟨84187120688897767305085547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56124747125931844870057031 84187120688897767305085547)
      ·
        refine ⟨126280681033346650957628321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84187120688897767305085547 126280681033346650957628321)
        ·
          refine ⟨94710510775009988218221241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126280681033346650957628321 94710510775009988218221241)
          ·
            refine ⟨71032883081257491163665931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94710510775009988218221241 71032883081257491163665931)
            ·
              refine ⟨106549324621886236745498897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71032883081257491163665931 106549324621886236745498897)
              ·
                refine ⟨79911993466414677559124173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106549324621886236745498897 79911993466414677559124173)
                ·
                  refine ⟨29966997549905504084671565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79911993466414677559124173 29966997549905504084671565)
                  ·
                    refine ⟨11237624081214564031751837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29966997549905504084671565 11237624081214564031751837)
                    ·
                      refine ⟨4214109030455461511906939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11237624081214564031751837 4214109030455461511906939)
                      ·
                        rfl

theorem cell23_8206948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_8206948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206948 prefixEnd_8206948 := by exact prefixLift 8206948
  have htrace : WordTrace (prefixWord ++ tailWord_8206948) baseStart_8206948 baseEnd_8206948 := by
    simpa [prefixWord, tailWord_8206948, baseEnd_8206948] using wordTrace_append hprefix tailTrace_8206948
  have hstable : (prefixWord ++ tailWord_8206948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206948).length < 2 ^ (prefixWord ++ tailWord_8206948).sum := by decide
  have hdescent : baseEnd_8206948 < baseStart_8206948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206961 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_8206961 : Nat := 118140960795 + 8206961 * 2 ^ 59
def prefixEnd_8206961 : Nat := 4983230072969 + 3 ^ 40 * 8206961 * 2
def baseEnd_8206961 : Nat := 4214115705703969961044379

theorem tailTrace_8206961 : CollatzResearch.WordTrace tailWord_8206961 prefixEnd_8206961 4214115705703969961044379 := by
  unfold tailWord_8206961
  simp only [CollatzResearch.WordTrace]
  refine ⟨299332458820589409193860737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199554972547059606129240491 299332458820589409193860737)
  ·
    refine ⟨224499344115442056895395553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299332458820589409193860737 224499344115442056895395553)
    ·
      refine ⟨168374508086581542671546665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224499344115442056895395553 168374508086581542671546665)
      ·
        refine ⟨126280881064936157003659999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168374508086581542671546665 126280881064936157003659999)
        ·
          refine ⟨189421321597404235505489999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126280881064936157003659999 189421321597404235505489999)
          ·
            refine ⟨284131982396106353258234999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189421321597404235505489999 284131982396106353258234999)
            ·
              refine ⟨426197973594159529887352499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284131982396106353258234999 426197973594159529887352499)
              ·
                refine ⟨639296960391239294831028749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426197973594159529887352499 639296960391239294831028749)
                ·
                  refine ⟨239736360146714735561635781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639296960391239294831028749 239736360146714735561635781)
                  ·
                    refine ⟨44950567527509012917806709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239736360146714735561635781 44950567527509012917806709)
                    ·
                      refine ⟨4214115705703969961044379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44950567527509012917806709 4214115705703969961044379)
                      ·
                        rfl

theorem cell23_8206961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_8206961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206961 prefixEnd_8206961 := by exact prefixLift 8206961
  have htrace : WordTrace (prefixWord ++ tailWord_8206961) baseStart_8206961 baseEnd_8206961 := by
    simpa [prefixWord, tailWord_8206961, baseEnd_8206961] using wordTrace_append hprefix tailTrace_8206961
  have hstable : (prefixWord ++ tailWord_8206961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206961).length < 2 ^ (prefixWord ++ tailWord_8206961).sum := by decide
  have hdescent : baseEnd_8206961 < baseStart_8206961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8206986 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_8206986 : Nat := 118140960795 + 8206986 * 2 ^ 59
def prefixEnd_8206986 : Nat := 4983230072969 + 3 ^ 40 * 8206986 * 2
def baseEnd_8206986 : Nat := 4214128542720332363231765

theorem tailTrace_8206986 : CollatzResearch.WordTrace tailWord_8206986 prefixEnd_8206986 4214128542720332363231765 := by
  unfold tailWord_8206986
  simp only [CollatzResearch.WordTrace]
  refine ⟨74833342661374709615880203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199555580430332558975680541 74833342661374709615880203)
  ·
    refine ⟨112250013992062064423820305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74833342661374709615880203 112250013992062064423820305)
    ·
      refine ⟨84187510494046548317865229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112250013992062064423820305 84187510494046548317865229)
      ·
        refine ⟨31570316435267455619199461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84187510494046548317865229 31570316435267455619199461)
        ·
          refine ⟨5919434331612647928599899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31570316435267455619199461 5919434331612647928599899)
          ·
            refine ⟨8879151497418971892899849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919434331612647928599899 8879151497418971892899849)
            ·
              refine ⟨6659363623064228919674887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8879151497418971892899849 6659363623064228919674887)
              ·
                refine ⟨9989045434596343379512331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659363623064228919674887 9989045434596343379512331)
                ·
                  refine ⟨14983568151894515069268497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9989045434596343379512331 14983568151894515069268497)
                  ·
                    refine ⟨11237676113920886301951373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14983568151894515069268497 11237676113920886301951373)
                    ·
                      refine ⟨4214128542720332363231765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11237676113920886301951373 4214128542720332363231765)
                      ·
                        rfl

theorem cell23_8206986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_8206986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8206986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8206986 prefixEnd_8206986 := by exact prefixLift 8206986
  have htrace : WordTrace (prefixWord ++ tailWord_8206986) baseStart_8206986 baseEnd_8206986 := by
    simpa [prefixWord, tailWord_8206986, baseEnd_8206986] using wordTrace_append hprefix tailTrace_8206986
  have hstable : (prefixWord ++ tailWord_8206986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8206986).length < 2 ^ (prefixWord ++ tailWord_8206986).sum := by decide
  have hdescent : baseEnd_8206986 < baseStart_8206986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8206986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207005 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_8207005 : Nat := 118140960795 + 8207005 * 2 ^ 59
def prefixEnd_8207005 : Nat := 4983230072969 + 3 ^ 40 * 8207005 * 2
def baseEnd_8207005 : Nat := 4214138298852767788894177

theorem tailTrace_8207005 : CollatzResearch.WordTrace tailWord_8207005 prefixEnd_8207005 4214138298852767788894177 := by
  unfold tailWord_8207005
  simp only [CollatzResearch.WordTrace]
  refine ⟨299334063632430004708462469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199556042421620003138974979 299334063632430004708462469)
  ·
    refine ⟨56125136931080625882836713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299334063632430004708462469 56125136931080625882836713)
    ·
      refine ⟨42093852698310469412127535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56125136931080625882836713 42093852698310469412127535)
      ·
        refine ⟨63140779047465704118191303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42093852698310469412127535 63140779047465704118191303)
        ·
          refine ⟨94711168571198556177286955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63140779047465704118191303 94711168571198556177286955)
          ·
            refine ⟨142066752856797834265930433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94711168571198556177286955 142066752856797834265930433)
            ·
              refine ⟨106550064642598375699447825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142066752856797834265930433 106550064642598375699447825)
              ·
                refine ⟨79912548481948781774585869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106550064642598375699447825 79912548481948781774585869)
                ·
                  refine ⟨29967205680730793165469701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79912548481948781774585869 29967205680730793165469701)
                  ·
                    refine ⟨5618851065137023718525569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29967205680730793165469701 5618851065137023718525569)
                    ·
                      refine ⟨4214138298852767788894177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618851065137023718525569 4214138298852767788894177)
                      ·
                        rfl

theorem cell23_8207005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_8207005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207005 prefixEnd_8207005 := by exact prefixLift 8207005
  have htrace : WordTrace (prefixWord ++ tailWord_8207005) baseStart_8207005 baseEnd_8207005 := by
    simpa [prefixWord, tailWord_8207005, baseEnd_8207005] using wordTrace_append hprefix tailTrace_8207005
  have hstable : (prefixWord ++ tailWord_8207005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207005).length < 2 ^ (prefixWord ++ tailWord_8207005).sum := by decide
  have hdescent : baseEnd_8207005 < baseStart_8207005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207065 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 2, 5, 2]
def baseStart_8207065 : Nat := 118140960795 + 8207065 * 2 ^ 59
def prefixEnd_8207065 : Nat := 4983230072969 + 3 ^ 40 * 8207065 * 2
def baseEnd_8207065 : Nat := 4214169107692037554143901

theorem tailTrace_8207065 : CollatzResearch.WordTrace tailWord_8207065 prefixEnd_8207065 4214169107692037554143901 := by
  unfold tailWord_8207065
  simp only [CollatzResearch.WordTrace]
  refine ⟨299336252012212634955646649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199557501341475089970431099 299336252012212634955646649)
  ·
    refine ⟨224502189009159476216734987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299336252012212634955646649 224502189009159476216734987)
    ·
      refine ⟨336753283513739214325102481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224502189009159476216734987 336753283513739214325102481)
      ·
        refine ⟨252564962635304410743826861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336753283513739214325102481 252564962635304410743826861)
        ·
          refine ⟨94711860988239154028935073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252564962635304410743826861 94711860988239154028935073)
          ·
            refine ⟨71033895741179365521701305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94711860988239154028935073 71033895741179365521701305)
            ·
              refine ⟨53275421805884524141275979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71033895741179365521701305 53275421805884524141275979)
              ·
                refine ⟨79913132708826786211913969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53275421805884524141275979 79913132708826786211913969)
                ·
                  refine ⟨59934849531620089658935477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79913132708826786211913969 59934849531620089658935477)
                  ·
                    refine ⟨5618892143589383405525201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59934849531620089658935477 5618892143589383405525201)
                    ·
                      refine ⟨4214169107692037554143901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618892143589383405525201 4214169107692037554143901)
                      ·
                        rfl

theorem cell23_8207065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_8207065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207065 prefixEnd_8207065 := by exact prefixLift 8207065
  have htrace : WordTrace (prefixWord ++ tailWord_8207065) baseStart_8207065 baseEnd_8207065 := by
    simpa [prefixWord, tailWord_8207065, baseEnd_8207065] using wordTrace_append hprefix tailTrace_8207065
  have hstable : (prefixWord ++ tailWord_8207065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207065).length < 2 ^ (prefixWord ++ tailWord_8207065).sum := by decide
  have hdescent : baseEnd_8207065 < baseStart_8207065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207095 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 4, 4, 2]
def baseStart_8207095 : Nat := 118140960795 + 8207095 * 2 ^ 59
def prefixEnd_8207095 : Nat := 4983230072969 + 3 ^ 40 * 8207095 * 2
def baseEnd_8207095 : Nat := 4214184512111672436768763

theorem tailTrace_8207095 : CollatzResearch.WordTrace tailWord_8207095 prefixEnd_8207095 4214184512111672436768763 := by
  unfold tailWord_8207095
  simp only [CollatzResearch.WordTrace]
  refine ⟨299337346202103950079238739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199558230801402633386159159 299337346202103950079238739)
  ·
    refine ⟨449006019303155925118858109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299337346202103950079238739 449006019303155925118858109)
    ·
      refine ⟨168377257238683471919571791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449006019303155925118858109 168377257238683471919571791)
      ·
        refine ⟨252565885858025207879357687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168377257238683471919571791 252565885858025207879357687)
        ·
          refine ⟨378848828787037811819036531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252565885858025207879357687 378848828787037811819036531)
          ·
            refine ⟨568273243180556717728554797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378848828787037811819036531 568273243180556717728554797)
            ·
              refine ⟨213102466192708769148208049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568273243180556717728554797 213102466192708769148208049)
              ·
                refine ⟨159826849644531576861156037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213102466192708769148208049 159826849644531576861156037)
                ·
                  refine ⟨29967534308349670661466757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159826849644531576861156037 29967534308349670661466757)
                  ·
                    refine ⟨5618912682815563249025017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29967534308349670661466757 5618912682815563249025017)
                    ·
                      refine ⟨4214184512111672436768763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5618912682815563249025017 4214184512111672436768763)
                      ·
                        rfl

theorem cell23_8207095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_8207095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207095 prefixEnd_8207095 := by exact prefixLift 8207095
  have htrace : WordTrace (prefixWord ++ tailWord_8207095) baseStart_8207095 baseEnd_8207095 := by
    simpa [prefixWord, tailWord_8207095, baseEnd_8207095] using wordTrace_append hprefix tailTrace_8207095
  have hstable : (prefixWord ++ tailWord_8207095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207095).length < 2 ^ (prefixWord ++ tailWord_8207095).sum := by decide
  have hdescent : baseEnd_8207095 < baseStart_8207095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207135 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 6]
def baseStart_8207135 : Nat := 118140960795 + 8207135 * 2 ^ 59
def prefixEnd_8207135 : Nat := 4983230072969 + 3 ^ 40 * 8207135 * 2
def baseEnd_8207135 : Nat := 468245005704205808918731

theorem tailTrace_8207135 : CollatzResearch.WordTrace tailWord_8207135 prefixEnd_8207135 468245005704205808918731 := by
  unfold tailWord_8207135
  simp only [CollatzResearch.WordTrace]
  refine ⟨299338805121959036910694859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199559203414639357940463239 299338805121959036910694859)
  ·
    refine ⟨449008207682938555366042289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299338805121959036910694859 449008207682938555366042289)
    ·
      refine ⟨336756155762203916524531717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449008207682938555366042289 336756155762203916524531717)
      ·
        refine ⟨63141779205413234348349697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336756155762203916524531717 63141779205413234348349697)
        ·
          refine ⟨47356334404059925761262273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63141779205413234348349697 47356334404059925761262273)
          ·
            refine ⟨35517250803044944320946705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47356334404059925761262273 35517250803044944320946705)
            ·
              refine ⟨26637938102283708240710029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35517250803044944320946705 26637938102283708240710029)
              ·
                refine ⟨9989226788356390590266261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26637938102283708240710029 9989226788356390590266261)
                ·
                  refine ⟨468245005704205808918731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9989226788356390590266261 468245005704205808918731)
                  ·
                    rfl

theorem cell23_8207135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 6].length) (baseStart_8207135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207135 prefixEnd_8207135 := by exact prefixLift 8207135
  have htrace : WordTrace (prefixWord ++ tailWord_8207135) baseStart_8207135 baseEnd_8207135 := by
    simpa [prefixWord, tailWord_8207135, baseEnd_8207135] using wordTrace_append hprefix tailTrace_8207135
  have hstable : (prefixWord ++ tailWord_8207135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207135).length < 2 ^ (prefixWord ++ tailWord_8207135).sum := by decide
  have hdescent : baseEnd_8207135 < baseStart_8207135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207146 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_8207146 : Nat := 118140960795 + 8207146 * 2 ^ 59
def prefixEnd_8207146 : Nat := 4983230072969 + 3 ^ 40 * 8207146 * 2
def baseEnd_8207146 : Nat := 4214210699625051737231029

theorem tailTrace_8207146 : CollatzResearch.WordTrace tailWord_8207146 prefixEnd_8207146 4214210699625051737231029 := by
  unfold tailWord_8207146
  simp only [CollatzResearch.WordTrace]
  refine ⟨74834801581229796447336323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199559470883279457192896861 74834801581229796447336323)
  ·
    refine ⟨112252202371844694671004485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74834801581229796447336323 112252202371844694671004485)
    ·
      refine ⟨21047287944720880250813341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112252202371844694671004485 21047287944720880250813341)
      ·
        refine ⟨7892732979270330094055003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21047287944720880250813341 7892732979270330094055003)
        ·
          refine ⟨11839099468905495141082505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7892732979270330094055003 11839099468905495141082505)
          ·
            refine ⟨8879324601679121355811879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11839099468905495141082505 8879324601679121355811879)
            ·
              refine ⟨13318986902518682033717819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879324601679121355811879 13318986902518682033717819)
              ·
                refine ⟨19978480353778023050576729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13318986902518682033717819 19978480353778023050576729)
                ·
                  refine ⟨14983860265333517287932547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19978480353778023050576729 14983860265333517287932547)
                  ·
                    refine ⟨22475790398000275931898821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14983860265333517287932547 22475790398000275931898821)
                    ·
                      refine ⟨4214210699625051737231029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22475790398000275931898821 4214210699625051737231029)
                      ·
                        rfl

theorem cell23_8207146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_8207146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207146 prefixEnd_8207146 := by exact prefixLift 8207146
  have htrace : WordTrace (prefixWord ++ tailWord_8207146) baseStart_8207146 baseEnd_8207146 := by
    simpa [prefixWord, tailWord_8207146, baseEnd_8207146] using wordTrace_append hprefix tailTrace_8207146
  have hstable : (prefixWord ++ tailWord_8207146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207146).length < 2 ^ (prefixWord ++ tailWord_8207146).sum := by decide
  have hdescent : baseEnd_8207146 < baseStart_8207146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207215 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_8207215 : Nat := 118140960795 + 8207215 * 2 ^ 59
def prefixEnd_8207215 : Nat := 4983230072969 + 3 ^ 40 * 8207215 * 2
def baseEnd_8207215 : Nat := 4214246129790211967268211

theorem tailTrace_8207215 : CollatzResearch.WordTrace tailWord_8207215 prefixEnd_8207215 4214246129790211967268211 := by
  unfold tailWord_8207215
  simp only [CollatzResearch.WordTrace]
  refine ⟨299341722961669210573607099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199561148641112807049071399 299341722961669210573607099)
  ·
    refine ⟨449012584442503815860410649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299341722961669210573607099 449012584442503815860410649)
    ·
      refine ⟨336759438331877861895307987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449012584442503815860410649 336759438331877861895307987)
      ·
        refine ⟨505139157497816792842961981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336759438331877861895307987 505139157497816792842961981)
        ·
          refine ⟨189427184061681297316110743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505139157497816792842961981 189427184061681297316110743)
          ·
            refine ⟨284140776092521945974166115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189427184061681297316110743 284140776092521945974166115)
            ·
              refine ⟨426211164138782918961249173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284140776092521945974166115 426211164138782918961249173)
              ·
                refine ⟨19978648319005449326308555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 426211164138782918961249173 19978648319005449326308555)
                ·
                  refine ⟨29967972478508173989462833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19978648319005449326308555 29967972478508173989462833)
                  ·
                    refine ⟨22475979358881130492097125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29967972478508173989462833 22475979358881130492097125)
                    ·
                      refine ⟨4214246129790211967268211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22475979358881130492097125 4214246129790211967268211)
                      ·
                        rfl

theorem cell23_8207215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_8207215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207215 prefixEnd_8207215 := by exact prefixLift 8207215
  have htrace : WordTrace (prefixWord ++ tailWord_8207215) baseStart_8207215 baseEnd_8207215 := by
    simpa [prefixWord, tailWord_8207215, baseEnd_8207215] using wordTrace_append hprefix tailTrace_8207215
  have hstable : (prefixWord ++ tailWord_8207215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207215).length < 2 ^ (prefixWord ++ tailWord_8207215).sum := by decide
  have hdescent : baseEnd_8207215 < baseStart_8207215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207225 : List Nat := [1, 2, 1, 3, 2, 5, 9]
def baseStart_8207225 : Nat := 118140960795 + 8207225 * 2 ^ 59
def prefixEnd_8207225 : Nat := 4983230072969 + 3 ^ 40 * 8207225 * 2
def baseEnd_8207225 : Nat := 52027793390083418865965

theorem tailTrace_8207225 : CollatzResearch.WordTrace tailWord_8207225 prefixEnd_8207225 52027793390083418865965 := by
  unfold tailWord_8207225
  simp only [CollatzResearch.WordTrace]
  refine ⟨299342087691632982281471129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199561391794421988187647419 299342087691632982281471129)
  ·
    refine ⟨224506565768724736711103347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299342087691632982281471129 224506565768724736711103347)
    ·
      refine ⟨336759848653087105066655021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224506565768724736711103347 336759848653087105066655021)
      ·
        refine ⟨126284943244907664399995633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336759848653087105066655021 126284943244907664399995633)
        ·
          refine ⟨94713707433680748299996725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126284943244907664399995633 94713707433680748299996725)
          ·
            refine ⟨8879410071907570153124693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94713707433680748299996725 8879410071907570153124693)
            ·
              refine ⟨52027793390083418865965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8879410071907570153124693 52027793390083418865965)
              ·
                rfl

theorem cell23_8207225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 9].length) (baseStart_8207225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207225 prefixEnd_8207225 := by exact prefixLift 8207225
  have htrace : WordTrace (prefixWord ++ tailWord_8207225) baseStart_8207225 baseEnd_8207225 := by
    simpa [prefixWord, tailWord_8207225, baseEnd_8207225] using wordTrace_append hprefix tailTrace_8207225
  have hstable : (prefixWord ++ tailWord_8207225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207225).length < 2 ^ (prefixWord ++ tailWord_8207225).sum := by decide
  have hdescent : baseEnd_8207225 < baseStart_8207225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207230 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_8207230 : Nat := 118140960795 + 8207230 * 2 ^ 59
def prefixEnd_8207230 : Nat := 4983230072969 + 3 ^ 40 * 8207230 * 2
def baseEnd_8207230 : Nat := 4214253832000029408580643

theorem tailTrace_8207230 : CollatzResearch.WordTrace tailWord_8207230 prefixEnd_8207230 4214253832000029408580643 := by
  unfold tailWord_8207230
  simp only [CollatzResearch.WordTrace]
  refine ⟨37417783757076858516925393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199561513371076578756935429 37417783757076858516925393)
  ·
    refine ⟨28063337817807643887694045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37417783757076858516925393 28063337817807643887694045)
    ·
      refine ⟨10523751681677866457885267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28063337817807643887694045 10523751681677866457885267)
      ·
        refine ⟨15785627522516799686827901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10523751681677866457885267 15785627522516799686827901)
        ·
          refine ⟨5919610320943799882560463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15785627522516799686827901 5919610320943799882560463)
          ·
            refine ⟨8879415481415699823840695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919610320943799882560463 8879415481415699823840695)
            ·
              refine ⟨13319123222123549735761043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879415481415699823840695 13319123222123549735761043)
              ·
                refine ⟨19978684833185324603641565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13319123222123549735761043 19978684833185324603641565)
                ·
                  refine ⟨7492006812444496726365587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19978684833185324603641565 7492006812444496726365587)
                  ·
                    refine ⟨11238010218666745089548381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492006812444496726365587 11238010218666745089548381)
                    ·
                      refine ⟨4214253832000029408580643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11238010218666745089548381 4214253832000029408580643)
                      ·
                        rfl

theorem cell23_8207230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_8207230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207230 prefixEnd_8207230 := by exact prefixLift 8207230
  have htrace : WordTrace (prefixWord ++ tailWord_8207230) baseStart_8207230 baseEnd_8207230 := by
    simpa [prefixWord, tailWord_8207230, baseEnd_8207230] using wordTrace_append hprefix tailTrace_8207230
  have hstable : (prefixWord ++ tailWord_8207230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207230).length < 2 ^ (prefixWord ++ tailWord_8207230).sum := by decide
  have hdescent : baseEnd_8207230 < baseStart_8207230 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207242 : List Nat := [3, 1, 2, 4, 1, 2, 2, 8]
def baseStart_8207242 : Nat := 118140960795 + 8207242 * 2 ^ 59
def prefixEnd_8207242 : Nat := 4983230072969 + 3 ^ 40 * 8207242 * 2
def baseEnd_8207242 : Nat := 156083703472884568949281

theorem tailTrace_8207242 : CollatzResearch.WordTrace tailWord_8207242 prefixEnd_8207242 156083703472884568949281 := by
  unfold tailWord_8207242
  simp only [CollatzResearch.WordTrace]
  refine ⟨74835676933142848546209995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199561805155047596123226653 74835676933142848546209995)
  ·
    refine ⟨112253515399714272819314993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74835676933142848546209995 112253515399714272819314993)
    ·
      refine ⟨84190136549785704614486245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112253515399714272819314993 84190136549785704614486245)
      ·
        refine ⟨15785650603084819615216171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84190136549785704614486245 15785650603084819615216171)
        ·
          refine ⟨23678475904627229422824257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15785650603084819615216171 23678475904627229422824257)
          ·
            refine ⟨17758856928470422067118193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23678475904627229422824257 17758856928470422067118193)
            ·
              refine ⟨13319142696352816550338645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17758856928470422067118193 13319142696352816550338645)
              ·
                refine ⟨156083703472884568949281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13319142696352816550338645 156083703472884568949281)
                ·
                  rfl

theorem cell23_8207242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 8].length) (baseStart_8207242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207242 prefixEnd_8207242 := by exact prefixLift 8207242
  have htrace : WordTrace (prefixWord ++ tailWord_8207242) baseStart_8207242 baseEnd_8207242 := by
    simpa [prefixWord, tailWord_8207242, baseEnd_8207242] using wordTrace_append hprefix tailTrace_8207242
  have hstable : (prefixWord ++ tailWord_8207242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207242).length < 2 ^ (prefixWord ++ tailWord_8207242).sum := by decide
  have hdescent : baseEnd_8207242 < baseStart_8207242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207295 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_8207295 : Nat := 118140960795 + 8207295 * 2 ^ 59
def prefixEnd_8207295 : Nat := 4983230072969 + 3 ^ 40 * 8207295 * 2
def baseEnd_8207295 : Nat := 4214287208242571654267843

theorem tailTrace_8207295 : CollatzResearch.WordTrace tailWord_8207295 prefixEnd_8207295 4214287208242571654267843 := by
  unfold tailWord_8207295
  simp only [CollatzResearch.WordTrace]
  refine ⟨299344640801379384236519339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199563093867586256157679559 299344640801379384236519339)
  ·
    refine ⟨449016961202069076354779009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299344640801379384236519339 449016961202069076354779009)
    ·
      refine ⟨336762720901551807266084257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449016961202069076354779009 336762720901551807266084257)
      ·
        refine ⟨252572040676163855449563193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336762720901551807266084257 252572040676163855449563193)
        ·
          refine ⟨189429030507122891587172395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252572040676163855449563193 189429030507122891587172395)
          ·
            refine ⟨284143545760684337380758593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189429030507122891587172395 284143545760684337380758593)
            ·
              refine ⟨213107659320513253035568945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284143545760684337380758593 213107659320513253035568945)
              ·
                refine ⟨159830744490384939776676709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213107659320513253035568945 159830744490384939776676709)
                ·
                  refine ⟨29968264591947176208126883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159830744490384939776676709 29968264591947176208126883)
                  ·
                    refine ⟨44952396887920764312190325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29968264591947176208126883 44952396887920764312190325)
                    ·
                      refine ⟨4214287208242571654267843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44952396887920764312190325 4214287208242571654267843)
                      ·
                        rfl

theorem cell23_8207295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_8207295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207295 prefixEnd_8207295 := by exact prefixLift 8207295
  have htrace : WordTrace (prefixWord ++ tailWord_8207295) baseStart_8207295 baseEnd_8207295 := by
    simpa [prefixWord, tailWord_8207295, baseEnd_8207295] using wordTrace_append hprefix tailTrace_8207295
  have hstable : (prefixWord ++ tailWord_8207295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207295).length < 2 ^ (prefixWord ++ tailWord_8207295).sum := by decide
  have hdescent : baseEnd_8207295 < baseStart_8207295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207330 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_8207330 : Nat := 118140960795 + 8207330 * 2 ^ 59
def prefixEnd_8207330 : Nat := 4983230072969 + 3 ^ 40 * 8207330 * 2
def baseEnd_8207330 : Nat := 4214305180065479017330183

theorem tailTrace_8207330 : CollatzResearch.WordTrace tailWord_8207330 prefixEnd_8207330 4214305180065479017330183 := by
  unfold tailWord_8207330
  simp only [CollatzResearch.WordTrace]
  refine ⟨74836479339063146303510861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199563944904168390142695629 74836479339063146303510861)
  ·
    refine ⟨28063679752148679863816573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74836479339063146303510861 28063679752148679863816573)
    ·
      refine ⟨10523879907055754948931215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28063679752148679863816573 10523879907055754948931215)
      ·
        refine ⟨15785819860583632423396823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10523879907055754948931215 15785819860583632423396823)
        ·
          refine ⟨23678729790875448635095235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15785819860583632423396823 23678729790875448635095235)
          ·
            refine ⟨35518094686313172952642853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23678729790875448635095235 35518094686313172952642853)
            ·
              refine ⟨6659642753683719928620535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35518094686313172952642853 6659642753683719928620535)
              ·
                refine ⟨9989464130525579892930803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659642753683719928620535 9989464130525579892930803)
                ·
                  refine ⟨14984196195788369839396205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9989464130525579892930803 14984196195788369839396205)
                  ·
                    refine ⟨5619073573420638689773577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14984196195788369839396205 5619073573420638689773577)
                    ·
                      refine ⟨4214305180065479017330183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619073573420638689773577 4214305180065479017330183)
                      ·
                        rfl

theorem cell23_8207330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_8207330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207330 prefixEnd_8207330 := by exact prefixLift 8207330
  have htrace : WordTrace (prefixWord ++ tailWord_8207330) baseStart_8207330 baseEnd_8207330 := by
    simpa [prefixWord, tailWord_8207330, baseEnd_8207330] using wordTrace_append hprefix tailTrace_8207330
  have hstable : (prefixWord ++ tailWord_8207330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207330).length < 2 ^ (prefixWord ++ tailWord_8207330).sum := by decide
  have hdescent : baseEnd_8207330 < baseStart_8207330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207343 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 2, 2, 2]
def baseStart_8207343 : Nat := 118140960795 + 8207343 * 2 ^ 59
def prefixEnd_8207343 : Nat := 4983230072969 + 3 ^ 40 * 8207343 * 2
def baseEnd_8207343 : Nat := 4214311855313987466467623

theorem tailTrace_8207343 : CollatzResearch.WordTrace tailWord_8207343 prefixEnd_8207343 4214311855313987466467623 := by
  unfold tailWord_8207343
  simp only [CollatzResearch.WordTrace]
  refine ⟨299346391505205488434266683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199564261003470325622844455 299346391505205488434266683)
  ·
    refine ⟨449019587257808232651400025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299346391505205488434266683 449019587257808232651400025)
    ·
      refine ⟨336764690443356174488550019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449019587257808232651400025 336764690443356174488550019)
      ·
        refine ⟨505147035665034261732825029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336764690443356174488550019 505147035665034261732825029)
        ·
          refine ⟨94715069187193924074904693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505147035665034261732825029 94715069187193924074904693)
          ·
            refine ⟨8879537736299430382022315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94715069187193924074904693 8879537736299430382022315)
            ·
              refine ⟨13319306604449145573033473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879537736299430382022315 13319306604449145573033473)
              ·
                refine ⟨9989479953336859179775105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13319306604449145573033473 9989479953336859179775105)
                ·
                  refine ⟨7492109965002644384831329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9989479953336859179775105 7492109965002644384831329)
                  ·
                    refine ⟨5619082473751983288623497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7492109965002644384831329 5619082473751983288623497)
                    ·
                      refine ⟨4214311855313987466467623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619082473751983288623497 4214311855313987466467623)
                      ·
                        rfl

theorem cell23_8207343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 2, 2].length) (baseStart_8207343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207343 prefixEnd_8207343 := by exact prefixLift 8207343
  have htrace : WordTrace (prefixWord ++ tailWord_8207343) baseStart_8207343 baseEnd_8207343 := by
    simpa [prefixWord, tailWord_8207343, baseEnd_8207343] using wordTrace_append hprefix tailTrace_8207343
  have hstable : (prefixWord ++ tailWord_8207343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207343).length < 2 ^ (prefixWord ++ tailWord_8207343).sum := by decide
  have hdescent : baseEnd_8207343 < baseStart_8207343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207355 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 7]
def baseStart_8207355 : Nat := 118140960795 + 8207355 * 2 ^ 59
def prefixEnd_8207355 : Nat := 4983230072969 + 3 ^ 40 * 8207355 * 2
def baseEnd_8207355 : Nat := 4214318017081841419517567

theorem tailTrace_8207355 : CollatzResearch.WordTrace tailWord_8207355 prefixEnd_8207355 4214318017081841419517567 := by
  unfold tailWord_8207355
  simp only [CollatzResearch.WordTrace]
  refine ⟨299346829181162014483703519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199564552787441342989135679 299346829181162014483703519)
  ·
    refine ⟨449020243771743021725555279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299346829181162014483703519 449020243771743021725555279)
    ·
      refine ⟨673530365657614532588332919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449020243771743021725555279 673530365657614532588332919)
      ·
        refine ⟨1010295548486421798882499379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673530365657614532588332919 1010295548486421798882499379)
        ·
          refine ⟨1515443322729632698323749069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010295548486421798882499379 1515443322729632698323749069)
          ·
            refine ⟨568291246023612261871405901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1515443322729632698323749069 568291246023612261871405901)
            ·
              refine ⟨213109217258854598201777213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568291246023612261871405901 213109217258854598201777213)
              ·
                refine ⟨79915956472070474325666455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213109217258854598201777213 79915956472070474325666455)
                ·
                  refine ⟨119873934708105711488499683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79915956472070474325666455 119873934708105711488499683)
                  ·
                    refine ⟨179810902062158567232749525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119873934708105711488499683 179810902062158567232749525)
                    ·
                      refine ⟨4214318017081841419517567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179810902062158567232749525 4214318017081841419517567)
                      ·
                        rfl

theorem cell23_8207355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_8207355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207355 prefixEnd_8207355 := by exact prefixLift 8207355
  have htrace : WordTrace (prefixWord ++ tailWord_8207355) baseStart_8207355 baseEnd_8207355 := by
    simpa [prefixWord, tailWord_8207355, baseEnd_8207355] using wordTrace_append hprefix tailTrace_8207355
  have hstable : (prefixWord ++ tailWord_8207355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207355).length < 2 ^ (prefixWord ++ tailWord_8207355).sum := by decide
  have hdescent : baseEnd_8207355 < baseStart_8207355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207449 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 3]
def baseStart_8207449 : Nat := 118140960795 + 8207449 * 2 ^ 59
def prefixEnd_8207449 : Nat := 4983230072969 + 3 ^ 40 * 8207449 * 2
def baseEnd_8207449 : Nat := 4214366284263364051742135

theorem tailTrace_8207449 : CollatzResearch.WordTrace tailWord_8207449 prefixEnd_8207449 4214366284263364051742135 := by
  unfold tailWord_8207449
  simp only [CollatzResearch.WordTrace]
  refine ⟨299350257642821468537625401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199566838428547645691750267 299350257642821468537625401)
  ·
    refine ⟨224512693232116101403219051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299350257642821468537625401 224512693232116101403219051)
    ·
      refine ⟨336769039848174152104828577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224512693232116101403219051 336769039848174152104828577)
      ·
        refine ⟨252576779886130614078621433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336769039848174152104828577 252576779886130614078621433)
        ·
          refine ⟨189432584914597960558966075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252576779886130614078621433 189432584914597960558966075)
          ·
            refine ⟨284148877371896940838449113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189432584914597960558966075 284148877371896940838449113)
            ·
              refine ⟨213111658028922705628836835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284148877371896940838449113 213111658028922705628836835)
              ·
                refine ⟨319667487043384058443255253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213111658028922705628836835 319667487043384058443255253)
                ·
                  refine ⟨7492206727579313869763795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 319667487043384058443255253 7492206727579313869763795)
                  ·
                    refine ⟨11238310091368970804645693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492206727579313869763795 11238310091368970804645693)
                    ·
                      refine ⟨4214366284263364051742135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11238310091368970804645693 4214366284263364051742135)
                      ·
                        rfl

theorem cell23_8207449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_8207449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207449 prefixEnd_8207449 := by exact prefixLift 8207449
  have htrace : WordTrace (prefixWord ++ tailWord_8207449) baseStart_8207449 baseEnd_8207449 := by
    simpa [prefixWord, tailWord_8207449, baseEnd_8207449] using wordTrace_append hprefix tailTrace_8207449
  have hstable : (prefixWord ++ tailWord_8207449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207449).length < 2 ^ (prefixWord ++ tailWord_8207449).sum := by decide
  have hdescent : baseEnd_8207449 < baseStart_8207449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207459 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 3, 5, 2]
def baseStart_8207459 : Nat := 118140960795 + 8207459 * 2 ^ 59
def prefixEnd_8207459 : Nat := 4983230072969 + 3 ^ 40 * 8207459 * 2
def baseEnd_8207459 : Nat := 4214371419069909012617089

theorem tailTrace_8207459 : CollatzResearch.WordTrace tailWord_8207459 prefixEnd_8207459 4214371419069909012617089 := by
  unfold tailWord_8207459
  simp only [CollatzResearch.WordTrace]
  refine ⟨299350622372785240245489431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199567081581856826830326287 299350622372785240245489431)
  ·
    refine ⟨449025933559177860368234147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299350622372785240245489431 449025933559177860368234147)
    ·
      refine ⟨673538900338766790552351221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449025933559177860368234147 673538900338766790552351221)
      ·
        refine ⟨63144271906759386614282927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 673538900338766790552351221 63144271906759386614282927)
        ·
          refine ⟨94716407860139079921424391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63144271906759386614282927 94716407860139079921424391)
          ·
            refine ⟨142074611790208619882136587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94716407860139079921424391 142074611790208619882136587)
            ·
              refine ⟨213111917685312929823204881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142074611790208619882136587 213111917685312929823204881)
              ·
                refine ⟨159833938263984697367403661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213111917685312929823204881 159833938263984697367403661)
                ·
                  refine ⟨59937726848994261512776373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159833938263984697367403661 59937726848994261512776373)
                  ·
                    refine ⟨5619161892093212016822785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59937726848994261512776373 5619161892093212016822785)
                    ·
                      refine ⟨4214371419069909012617089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619161892093212016822785 4214371419069909012617089)
                      ·
                        rfl

theorem cell23_8207459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_8207459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207459 prefixEnd_8207459 := by exact prefixLift 8207459
  have htrace : WordTrace (prefixWord ++ tailWord_8207459) baseStart_8207459 baseEnd_8207459 := by
    simpa [prefixWord, tailWord_8207459, baseEnd_8207459] using wordTrace_append hprefix tailTrace_8207459
  have hstable : (prefixWord ++ tailWord_8207459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207459).length < 2 ^ (prefixWord ++ tailWord_8207459).sum := by decide
  have hdescent : baseEnd_8207459 < baseStart_8207459 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207469 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_8207469 : Nat := 118140960795 + 8207469 * 2 ^ 59
def prefixEnd_8207469 : Nat := 4983230072969 + 3 ^ 40 * 8207469 * 2
def baseEnd_8207469 : Nat := 1404792184625484657830681

theorem tailTrace_8207469 : CollatzResearch.WordTrace tailWord_8207469 prefixEnd_8207469 1404792184625484657830681 := by
  unfold tailWord_8207469
  simp only [CollatzResearch.WordTrace]
  refine ⟨299350987102749011953353461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199567324735166007968902307 299350987102749011953353461)
  ·
    refine ⟨28064155040882719870626887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299350987102749011953353461 28064155040882719870626887)
    ·
      refine ⟨42096232561324079805940331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28064155040882719870626887 42096232561324079805940331)
      ·
        refine ⟨63144348841986119708910497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42096232561324079805940331 63144348841986119708910497)
        ·
          refine ⟨47358261631489589781682873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63144348841986119708910497 47358261631489589781682873)
          ·
            refine ⟨35518696223617192336262155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47358261631489589781682873 35518696223617192336262155)
            ·
              refine ⟨53278044335425788504393233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35518696223617192336262155 53278044335425788504393233)
              ·
                refine ⟨39958533251569341378294925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53278044335425788504393233 39958533251569341378294925)
                ·
                  refine ⟨14984449969338503016860597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39958533251569341378294925 14984449969338503016860597)
                  ·
                    refine ⟨1404792184625484657830681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14984449969338503016860597 1404792184625484657830681)
                    ·
                      rfl

theorem cell23_8207469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_8207469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207469 prefixEnd_8207469 := by exact prefixLift 8207469
  have htrace : WordTrace (prefixWord ++ tailWord_8207469) baseStart_8207469 baseEnd_8207469 := by
    simpa [prefixWord, tailWord_8207469, baseEnd_8207469] using wordTrace_append hprefix tailTrace_8207469
  have hstable : (prefixWord ++ tailWord_8207469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207469).length < 2 ^ (prefixWord ++ tailWord_8207469).sum := by decide
  have hdescent : baseEnd_8207469 < baseStart_8207469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207509 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_8207509 : Nat := 118140960795 + 8207509 * 2 ^ 59
def prefixEnd_8207509 : Nat := 4983230072969 + 3 ^ 40 * 8207509 * 2
def baseEnd_8207509 : Nat := 4214397093102633816991859

theorem tailTrace_8207509 : CollatzResearch.WordTrace tailWord_8207509 prefixEnd_8207509 4214397093102633816991859 := by
  unfold tailWord_8207509
  simp only [CollatzResearch.WordTrace]
  refine ⟨299352446022604098784809581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199568297348402732523206387 299352446022604098784809581)
  ·
    refine ⟨112257167258476537044303593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299352446022604098784809581 112257167258476537044303593)
    ·
      refine ⟨84192875443857402783227695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112257167258476537044303593 84192875443857402783227695)
      ·
        refine ⟨126289313165786104174841543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84192875443857402783227695 126289313165786104174841543)
        ·
          refine ⟨189433969748679156262262315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126289313165786104174841543 189433969748679156262262315)
          ·
            refine ⟨284150954623018734393393473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189433969748679156262262315 284150954623018734393393473)
            ·
              refine ⟨213113215967264050795045105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284150954623018734393393473 213113215967264050795045105)
              ·
                refine ⟨159834911975448038096283829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213113215967264050795045105 159834911975448038096283829)
                ·
                  refine ⟨14984522997698253571526609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159834911975448038096283829 14984522997698253571526609)
                  ·
                    refine ⟨11238392248273690178644957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14984522997698253571526609 11238392248273690178644957)
                    ·
                      refine ⟨4214397093102633816991859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11238392248273690178644957 4214397093102633816991859)
                      ·
                        rfl

theorem cell23_8207509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_8207509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207509 prefixEnd_8207509 := by exact prefixLift 8207509
  have htrace : WordTrace (prefixWord ++ tailWord_8207509) baseStart_8207509 baseEnd_8207509 := by
    simpa [prefixWord, tailWord_8207509, baseEnd_8207509] using wordTrace_append hprefix tailTrace_8207509
  have hstable : (prefixWord ++ tailWord_8207509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207509).length < 2 ^ (prefixWord ++ tailWord_8207509).sum := by decide
  have hdescent : baseEnd_8207509 < baseStart_8207509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207516 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_8207516 : Nat := 118140960795 + 8207516 * 2 ^ 59
def prefixEnd_8207516 : Nat := 4983230072969 + 3 ^ 40 * 8207516 * 2
def baseEnd_8207516 : Nat := 1404800229155738429868109

theorem tailTrace_8207516 : CollatzResearch.WordTrace tailWord_8207516 prefixEnd_8207516 1404800229155738429868109 := by
  unfold tailWord_8207516
  simp only [CollatzResearch.WordTrace]
  refine ⟨149676350666789369490157201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199568467555719159320209601 149676350666789369490157201)
  ·
    refine ⟨112257263000092027117617901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149676350666789369490157201 112257263000092027117617901)
    ·
      refine ⟨42096473625034510169106713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112257263000092027117617901 42096473625034510169106713)
      ·
        refine ⟨31572355218775882626830035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42096473625034510169106713 31572355218775882626830035)
        ·
          refine ⟨47358532828163823940245053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31572355218775882626830035 47358532828163823940245053)
          ·
            refine ⟨17759449810561433977591895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47358532828163823940245053 17759449810561433977591895)
            ·
              refine ⟨26639174715842150966387843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17759449810561433977591895 26639174715842150966387843)
              ·
                refine ⟨39958762073763226449581765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26639174715842150966387843 39958762073763226449581765)
                ·
                  refine ⟨7492267888830604959296581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39958762073763226449581765 7492267888830604959296581)
                  ·
                    refine ⟨1404800229155738429868109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492267888830604959296581 1404800229155738429868109)
                    ·
                      rfl

theorem cell23_8207516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_8207516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207516 prefixEnd_8207516 := by exact prefixLift 8207516
  have htrace : WordTrace (prefixWord ++ tailWord_8207516) baseStart_8207516 baseEnd_8207516 := by
    simpa [prefixWord, tailWord_8207516, baseEnd_8207516] using wordTrace_append hprefix tailTrace_8207516
  have hstable : (prefixWord ++ tailWord_8207516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207516).length < 2 ^ (prefixWord ++ tailWord_8207516).sum := by decide
  have hdescent : baseEnd_8207516 < baseStart_8207516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207532 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_8207532 : Nat := 118140960795 + 8207532 * 2 ^ 59
def prefixEnd_8207532 : Nat := 4983230072969 + 3 ^ 40 * 8207532 * 2
def baseEnd_8207532 : Nat := 4214408903157687227004253

theorem tailTrace_8207532 : CollatzResearch.WordTrace tailWord_8207532 prefixEnd_8207532 4214408903157687227004253 := by
  unfold tailWord_8207532
  simp only [CollatzResearch.WordTrace]
  refine ⟨149676642450760386856448425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199568856601013849141931233 149676642450760386856448425)
  ·
    refine ⟨112257481838070290142336319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149676642450760386856448425 112257481838070290142336319)
    ·
      refine ⟨168386222757105435213504479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112257481838070290142336319 168386222757105435213504479)
      ·
        refine ⟨252579334135658152820256719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168386222757105435213504479 252579334135658152820256719)
        ·
          refine ⟨378869001203487229230385079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252579334135658152820256719 378869001203487229230385079)
          ·
            refine ⟨568303501805230843845577619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378869001203487229230385079 568303501805230843845577619)
            ·
              refine ⟨852455252707846265768366429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568303501805230843845577619 852455252707846265768366429)
              ·
                refine ⟨319670719765442349663137411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 852455252707846265768366429 319670719765442349663137411)
                ·
                  refine ⟨479506079648163524494706117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319670719765442349663137411 479506079648163524494706117)
                  ·
                    refine ⟨89907389934030660842757397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 479506079648163524494706117 89907389934030660842757397)
                    ·
                      refine ⟨4214408903157687227004253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89907389934030660842757397 4214408903157687227004253)
                      ·
                        rfl

theorem cell23_8207532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_8207532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207532 prefixEnd_8207532 := by exact prefixLift 8207532
  have htrace : WordTrace (prefixWord ++ tailWord_8207532) baseStart_8207532 baseEnd_8207532 := by
    simpa [prefixWord, tailWord_8207532, baseEnd_8207532] using wordTrace_append hprefix tailTrace_8207532
  have hstable : (prefixWord ++ tailWord_8207532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207532).length < 2 ^ (prefixWord ++ tailWord_8207532).sum := by decide
  have hdescent : baseEnd_8207532 < baseStart_8207532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207533 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_8207533 : Nat := 118140960795 + 8207533 * 2 ^ 59
def prefixEnd_8207533 : Nat := 4983230072969 + 3 ^ 40 * 8207533 * 2
def baseEnd_8207533 : Nat := 1404803138879447241030583

theorem tailTrace_8207533 : CollatzResearch.WordTrace tailWord_8207533 prefixEnd_8207533 1404803138879447241030583 := by
  unfold tailWord_8207533
  simp only [CollatzResearch.WordTrace]
  refine ⟨299353321374517150883683253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199568880916344767255788835 299353321374517150883683253)
  ·
    refine ⟨28064373878860982895345305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299353321374517150883683253 28064373878860982895345305)
    ·
      refine ⟨21048280409145737171508979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28064373878860982895345305 21048280409145737171508979)
      ·
        refine ⟨31572420613718605757263469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21048280409145737171508979 31572420613718605757263469)
        ·
          refine ⟨11839657730144477158973801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31572420613718605757263469 11839657730144477158973801)
          ·
            refine ⟨8879743297608357869230351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11839657730144477158973801 8879743297608357869230351)
            ·
              refine ⟨13319614946412536803845527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879743297608357869230351 13319614946412536803845527)
              ·
                refine ⟨19979422419618805205768291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13319614946412536803845527 19979422419618805205768291)
                ·
                  refine ⟨29969133629428207808652437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19979422419618805205768291 29969133629428207808652437)
                  ·
                    refine ⟨1404803138879447241030583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29969133629428207808652437 1404803138879447241030583)
                    ·
                      rfl

theorem cell23_8207533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_8207533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207533 prefixEnd_8207533 := by exact prefixLift 8207533
  have htrace : WordTrace (prefixWord ++ tailWord_8207533) baseStart_8207533 baseEnd_8207533 := by
    simpa [prefixWord, tailWord_8207533, baseEnd_8207533] using wordTrace_append hprefix tailTrace_8207533
  have hstable : (prefixWord ++ tailWord_8207533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207533).length < 2 ^ (prefixWord ++ tailWord_8207533).sum := by decide
  have hdescent : baseEnd_8207533 < baseStart_8207533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207573 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_8207573 : Nat := 118140960795 + 8207573 * 2 ^ 59
def prefixEnd_8207573 : Nat := 4983230072969 + 3 ^ 40 * 8207573 * 2
def baseEnd_8207573 : Nat := 4214429955864521566591565

theorem tailTrace_8207573 : CollatzResearch.WordTrace tailWord_8207573 prefixEnd_8207573 4214429955864521566591565 := by
  unfold tailWord_8207573
  simp only [CollatzResearch.WordTrace]
  refine ⟨299354780294372237715139373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199569853529581491810092915 299354780294372237715139373)
  ·
    refine ⟨112258042610389589143177265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299354780294372237715139373 112258042610389589143177265)
    ·
      refine ⟨84193531957792191857382949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112258042610389589143177265 84193531957792191857382949)
      ·
        refine ⟨15786287242086035973259303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84193531957792191857382949 15786287242086035973259303)
        ·
          refine ⟨23679430863129053959888955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15786287242086035973259303 23679430863129053959888955)
          ·
            refine ⟨35519146294693580939833433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23679430863129053959888955 35519146294693580939833433)
            ·
              refine ⟨26639359721020185704875075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35519146294693580939833433 26639359721020185704875075)
              ·
                refine ⟨39959039581530278557312613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26639359721020185704875075 39959039581530278557312613)
                ·
                  refine ⟨7492319921536927229496115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39959039581530278557312613 7492319921536927229496115)
                  ·
                    refine ⟨11238479882305390844244173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492319921536927229496115 11238479882305390844244173)
                    ·
                      refine ⟨4214429955864521566591565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11238479882305390844244173 4214429955864521566591565)
                      ·
                        rfl

theorem cell23_8207573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_8207573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207573 prefixEnd_8207573 := by exact prefixLift 8207573
  have htrace : WordTrace (prefixWord ++ tailWord_8207573) baseStart_8207573 baseEnd_8207573 := by
    simpa [prefixWord, tailWord_8207573, baseEnd_8207573] using wordTrace_append hprefix tailTrace_8207573
  have hstable : (prefixWord ++ tailWord_8207573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207573).length < 2 ^ (prefixWord ++ tailWord_8207573).sum := by decide
  have hdescent : baseEnd_8207573 < baseStart_8207573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207574 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_8207574 : Nat := 118140960795 + 8207574 * 2 ^ 59
def prefixEnd_8207574 : Nat := 4983230072969 + 3 ^ 40 * 8207574 * 2
def baseEnd_8207574 : Nat := 4214430469345176062679061

theorem tailTrace_8207574 : CollatzResearch.WordTrace tailWord_8207574 prefixEnd_8207574 4214430469345176062679061 := by
  unfold tailWord_8207574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18709676047960538430370361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199569877844912409923950517 18709676047960538430370361)
  ·
    refine ⟨14032257035970403822777771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18709676047960538430370361 14032257035970403822777771)
    ·
      refine ⟨21048385553955605734166657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14032257035970403822777771 21048385553955605734166657)
      ·
        refine ⟨15786289165466704300624993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21048385553955605734166657 15786289165466704300624993)
        ·
          refine ⟨11839716874100028225468745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15786289165466704300624993 11839716874100028225468745)
          ·
            refine ⟨8879787655575021169101559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11839716874100028225468745 8879787655575021169101559)
            ·
              refine ⟨13319681483362531753652339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879787655575021169101559 13319681483362531753652339)
              ·
                refine ⟨19979522225043797630478509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13319681483362531753652339 19979522225043797630478509)
                ·
                  refine ⟨7492320834391424111429441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19979522225043797630478509 7492320834391424111429441)
                  ·
                    refine ⟨5619240625793568083572081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7492320834391424111429441 5619240625793568083572081)
                    ·
                      refine ⟨4214430469345176062679061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619240625793568083572081 4214430469345176062679061)
                      ·
                        rfl

theorem cell23_8207574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_8207574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207574 prefixEnd_8207574 := by exact prefixLift 8207574
  have htrace : WordTrace (prefixWord ++ tailWord_8207574) baseStart_8207574 baseEnd_8207574 := by
    simpa [prefixWord, tailWord_8207574, baseEnd_8207574] using wordTrace_append hprefix tailTrace_8207574
  have hstable : (prefixWord ++ tailWord_8207574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207574).length < 2 ^ (prefixWord ++ tailWord_8207574).sum := by decide
  have hdescent : baseEnd_8207574 < baseStart_8207574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207630 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_8207630 : Nat := 118140960795 + 8207630 * 2 ^ 59
def prefixEnd_8207630 : Nat := 4983230072969 + 3 ^ 40 * 8207630 * 2
def baseEnd_8207630 : Nat := 4214459224261827843578803

theorem tailTrace_8207630 : CollatzResearch.WordTrace tailWord_8207630 prefixEnd_8207630 4214459224261827843578803 := by
  unfold tailWord_8207630
  simp only [CollatzResearch.WordTrace]
  refine ⟨37419607406895717056245543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199571239503443824299976229 37419607406895717056245543)
  ·
    refine ⟨56129411110343575584368315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37419607406895717056245543 56129411110343575584368315)
    ·
      refine ⟨84194116665515363376552473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56129411110343575584368315 84194116665515363376552473)
      ·
        refine ⟨63145587499136522532414355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84194116665515363376552473 63145587499136522532414355)
        ·
          refine ⟨94718381248704783798621533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63145587499136522532414355 94718381248704783798621533)
          ·
            refine ⟨35519392968264293924483075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94718381248704783798621533 35519392968264293924483075)
            ·
              refine ⟨53279089452396440886724613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35519392968264293924483075 53279089452396440886724613)
              ·
                refine ⟨9989829272324332666260865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53279089452396440886724613 9989829272324332666260865)
                ·
                  refine ⟨7492371954243249499695649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9989829272324332666260865 7492371954243249499695649)
                  ·
                    refine ⟨5619278965682437124771737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7492371954243249499695649 5619278965682437124771737)
                    ·
                      refine ⟨4214459224261827843578803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619278965682437124771737 4214459224261827843578803)
                      ·
                        rfl

theorem cell23_8207630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_8207630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207630 prefixEnd_8207630 := by exact prefixLift 8207630
  have htrace : WordTrace (prefixWord ++ tailWord_8207630) baseStart_8207630 baseEnd_8207630 := by
    simpa [prefixWord, tailWord_8207630, baseEnd_8207630] using wordTrace_append hprefix tailTrace_8207630
  have hstable : (prefixWord ++ tailWord_8207630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207630).length < 2 ^ (prefixWord ++ tailWord_8207630).sum := by decide
  have hdescent : baseEnd_8207630 < baseStart_8207630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207649 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 1, 7]
def baseStart_8207649 : Nat := 118140960795 + 8207649 * 2 ^ 59
def prefixEnd_8207649 : Nat := 4983230072969 + 3 ^ 40 * 8207649 * 2
def baseEnd_8207649 : Nat := 1404822993464754423080405

theorem tailTrace_8207649 : CollatzResearch.WordTrace tailWord_8207649 prefixEnd_8207649 1404822993464754423080405 := by
  unfold tailWord_8207649
  simp only [CollatzResearch.WordTrace]
  refine ⟨299357552242096902694906001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199571701494731268463270667 299357552242096902694906001)
  ·
    refine ⟨224518164181572677021179501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299357552242096902694906001 224518164181572677021179501)
    ·
      refine ⟨84194311568089753882942313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224518164181572677021179501 84194311568089753882942313)
      ·
        refine ⟨63145733676067315412206735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84194311568089753882942313 63145733676067315412206735)
        ·
          refine ⟨94718600514100973118310103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63145733676067315412206735 94718600514100973118310103)
          ·
            refine ⟨142077900771151459677465155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94718600514100973118310103 142077900771151459677465155)
            ·
              refine ⟨213116851156727189516197733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142077900771151459677465155 213116851156727189516197733)
              ·
                refine ⟨39959409591886348034287075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213116851156727189516197733 39959409591886348034287075)
                ·
                  refine ⟨59939114387829522051430613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39959409591886348034287075 59939114387829522051430613)
                  ·
                    refine ⟨1404822993464754423080405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59939114387829522051430613 1404822993464754423080405)
                    ·
                      rfl

theorem cell23_8207649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_8207649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207649 prefixEnd_8207649 := by exact prefixLift 8207649
  have htrace : WordTrace (prefixWord ++ tailWord_8207649) baseStart_8207649 baseEnd_8207649 := by
    simpa [prefixWord, tailWord_8207649, baseEnd_8207649] using wordTrace_append hprefix tailTrace_8207649
  have hstable : (prefixWord ++ tailWord_8207649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207649).length < 2 ^ (prefixWord ++ tailWord_8207649).sum := by decide
  have hdescent : baseEnd_8207649 < baseStart_8207649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207666 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_8207666 : Nat := 118140960795 + 8207666 * 2 ^ 59
def prefixEnd_8207666 : Nat := 4983230072969 + 3 ^ 40 * 8207666 * 2
def baseEnd_8207666 : Nat := 1404825903188463234242879

theorem tailTrace_8207666 : CollatzResearch.WordTrace tailWord_8207666 prefixEnd_8207666 1404825903188463234242879 := by
  unfold tailWord_8207666
  simp only [CollatzResearch.WordTrace]
  refine ⟨74839543070758828649568713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199572114855356876398849901 74839543070758828649568713)
  ·
    refine ⟨56129657303069121487176535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74839543070758828649568713 56129657303069121487176535)
    ·
      refine ⟨84194485954603682230764803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56129657303069121487176535 84194485954603682230764803)
      ·
        refine ⟨126291728931905523346147205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84194485954603682230764803 126291728931905523346147205)
        ·
          refine ⟨23679699174732285627402601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126291728931905523346147205 23679699174732285627402601)
          ·
            refine ⟨17759774381049214220551951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23679699174732285627402601 17759774381049214220551951)
            ·
              refine ⟨26639661571573821330827927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17759774381049214220551951 26639661571573821330827927)
              ·
                refine ⟨39959492357360731996241891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26639661571573821330827927 39959492357360731996241891)
                ·
                  refine ⟨59939238536041097994362837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39959492357360731996241891 59939238536041097994362837)
                  ·
                    refine ⟨1404825903188463234242879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59939238536041097994362837 1404825903188463234242879)
                    ·
                      rfl

theorem cell23_8207666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_8207666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207666 prefixEnd_8207666 := by exact prefixLift 8207666
  have htrace : WordTrace (prefixWord ++ tailWord_8207666) baseStart_8207666 baseEnd_8207666 := by
    simpa [prefixWord, tailWord_8207666, baseEnd_8207666] using wordTrace_append hprefix tailTrace_8207666
  have hstable : (prefixWord ++ tailWord_8207666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207666).length < 2 ^ (prefixWord ++ tailWord_8207666).sum := by decide
  have hdescent : baseEnd_8207666 < baseStart_8207666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207689 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_8207689 : Nat := 118140960795 + 8207689 * 2 ^ 59
def prefixEnd_8207689 : Nat := 4983230072969 + 3 ^ 40 * 8207689 * 2
def baseEnd_8207689 : Nat := 4214489519620443112741031

theorem tailTrace_8207689 : CollatzResearch.WordTrace tailWord_8207689 prefixEnd_8207689 4214489519620443112741031 := by
  unfold tailWord_8207689
  simp only [CollatzResearch.WordTrace]
  refine ⟨299359011161951989526362121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199572674107967993017574747 299359011161951989526362121)
  ·
    refine ⟨224519258371463992144771591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299359011161951989526362121 224519258371463992144771591)
    ·
      refine ⟨336778887557195988217157387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224519258371463992144771591 336778887557195988217157387)
      ·
        refine ⟨505168331335793982325736081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336778887557195988217157387 505168331335793982325736081)
        ·
          refine ⟨378876248501845486744302061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505168331335793982325736081 378876248501845486744302061)
          ·
            refine ⟨142078593188192057529113273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378876248501845486744302061 142078593188192057529113273)
            ·
              refine ⟨106558944891144043146834955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142078593188192057529113273 106558944891144043146834955)
              ·
                refine ⟨159838417336716064720252433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106558944891144043146834955 159838417336716064720252433)
                ·
                  refine ⟨119878813002537048540189325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159838417336716064720252433 119878813002537048540189325)
                  ·
                    refine ⟨44954554875951393202570997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119878813002537048540189325 44954554875951393202570997)
                    ·
                      refine ⟨4214489519620443112741031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44954554875951393202570997 4214489519620443112741031)
                      ·
                        rfl

theorem cell23_8207689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_8207689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207689 prefixEnd_8207689 := by exact prefixLift 8207689
  have htrace : WordTrace (prefixWord ++ tailWord_8207689) baseStart_8207689 baseEnd_8207689 := by
    simpa [prefixWord, tailWord_8207689, baseEnd_8207689] using wordTrace_append hprefix tailTrace_8207689
  have hstable : (prefixWord ++ tailWord_8207689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207689).length < 2 ^ (prefixWord ++ tailWord_8207689).sum := by decide
  have hdescent : baseEnd_8207689 < baseStart_8207689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207699 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 6]
def baseStart_8207699 : Nat := 118140960795 + 8207699 * 2 ^ 59
def prefixEnd_8207699 : Nat := 4983230072969 + 3 ^ 40 * 8207699 * 2
def baseEnd_8207699 : Nat := 4214494654426988073615985

theorem tailTrace_8207699 : CollatzResearch.WordTrace tailWord_8207699 prefixEnd_8207699 4214494654426988073615985 := by
  unfold tailWord_8207699
  simp only [CollatzResearch.WordTrace]
  refine ⟨299359375891915761234226151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199572917261277174156150767 299359375891915761234226151)
  ·
    refine ⟨449039063837873641851339227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299359375891915761234226151 449039063837873641851339227)
    ·
      refine ⟨673558595756810462777008841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449039063837873641851339227 673558595756810462777008841)
      ·
        refine ⟨505168946817607847082756631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673558595756810462777008841 505168946817607847082756631)
        ·
          refine ⟨757753420226411770624134947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505168946817607847082756631 757753420226411770624134947)
          ·
            refine ⟨1136630130339617655936202421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757753420226411770624134947 1136630130339617655936202421)
            ·
              refine ⟨106559074719339155244018977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1136630130339617655936202421 106559074719339155244018977)
              ·
                refine ⟨79919306039504366433014233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106559074719339155244018977 79919306039504366433014233)
                ·
                  refine ⟨59939479529628274824760675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79919306039504366433014233 59939479529628274824760675)
                  ·
                    refine ⟨89909219294442412237141013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59939479529628274824760675 89909219294442412237141013)
                    ·
                      refine ⟨4214494654426988073615985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89909219294442412237141013 4214494654426988073615985)
                      ·
                        rfl

theorem cell23_8207699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_8207699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207699 prefixEnd_8207699 := by exact prefixLift 8207699
  have htrace : WordTrace (prefixWord ++ tailWord_8207699) baseStart_8207699 baseEnd_8207699 := by
    simpa [prefixWord, tailWord_8207699, baseEnd_8207699] using wordTrace_append hprefix tailTrace_8207699
  have hstable : (prefixWord ++ tailWord_8207699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207699).length < 2 ^ (prefixWord ++ tailWord_8207699).sum := by decide
  have hdescent : baseEnd_8207699 < baseStart_8207699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207703 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 2, 4, 2]
def baseStart_8207703 : Nat := 118140960795 + 8207703 * 2 ^ 59
def prefixEnd_8207703 : Nat := 4983230072969 + 3 ^ 40 * 8207703 * 2
def baseEnd_8207703 : Nat := 4214496708349606057965967

theorem tailTrace_8207703 : CollatzResearch.WordTrace tailWord_8207703 prefixEnd_8207703 4214496708349606057965967 := by
  unfold tailWord_8207703
  simp only [CollatzResearch.WordTrace]
  refine ⟨299359521783901269917371763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199573014522600846611581175 299359521783901269917371763)
  ·
    refine ⟨449039282675851904876057645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299359521783901269917371763 449039282675851904876057645)
    ·
      refine ⟨168389731003444464328521617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449039282675851904876057645 168389731003444464328521617)
      ·
        refine ⟨126292298252583348246391213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168389731003444464328521617 126292298252583348246391213)
        ·
          refine ⟨47359611844718755592396705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126292298252583348246391213 47359611844718755592396705)
          ·
            refine ⟨35519708883539066694297529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47359611844718755592396705 35519708883539066694297529)
            ·
              refine ⟨26639781662654300020723147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35519708883539066694297529 26639781662654300020723147)
              ·
                refine ⟨39959672493981450031084721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26639781662654300020723147 39959672493981450031084721)
                ·
                  refine ⟨29969754370486087523313541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39959672493981450031084721 29969754370486087523313541)
                  ·
                    refine ⟨5619328944466141410621289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29969754370486087523313541 5619328944466141410621289)
                    ·
                      refine ⟨4214496708349606057965967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619328944466141410621289 4214496708349606057965967)
                      ·
                        rfl

theorem cell23_8207703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_8207703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207703 prefixEnd_8207703 := by exact prefixLift 8207703
  have htrace : WordTrace (prefixWord ++ tailWord_8207703) baseStart_8207703 baseEnd_8207703 := by
    simpa [prefixWord, tailWord_8207703, baseEnd_8207703] using wordTrace_append hprefix tailTrace_8207703
  have hstable : (prefixWord ++ tailWord_8207703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207703).length < 2 ^ (prefixWord ++ tailWord_8207703).sum := by decide
  have hdescent : baseEnd_8207703 < baseStart_8207703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207706 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_8207706 : Nat := 118140960795 + 8207706 * 2 ^ 59
def prefixEnd_8207706 : Nat := 4983230072969 + 3 ^ 40 * 8207706 * 2
def baseEnd_8207706 : Nat := 4214498248791569546228453

theorem tailTrace_8207706 : CollatzResearch.WordTrace tailWord_8207706 prefixEnd_8207706 4214498248791569546228453 := by
  unfold tailWord_8207706
  simp only [CollatzResearch.WordTrace]
  refine ⟨74839907800722600357432743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199573087468593600953153981 74839907800722600357432743)
  ·
    refine ⟨112259861701083900536149115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74839907800722600357432743 112259861701083900536149115)
    ·
      refine ⟨168389792551625850804223673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112259861701083900536149115 168389792551625850804223673)
      ·
        refine ⟨126292344413719388103167755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168389792551625850804223673 126292344413719388103167755)
        ·
          refine ⟨189438516620579082154751633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126292344413719388103167755 189438516620579082154751633)
          ·
            refine ⟨142078887465434311616063725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189438516620579082154751633 142078887465434311616063725)
            ·
              refine ⟨53279582799537866856023897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142078887465434311616063725 53279582799537866856023897)
              ·
                refine ⟨39959687099653400142017923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53279582799537866856023897 39959687099653400142017923)
                ·
                  refine ⟨59939530649480100213026885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39959687099653400142017923 59939530649480100213026885)
                  ·
                    refine ⟨11238661996777518789942541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59939530649480100213026885 11238661996777518789942541)
                    ·
                      refine ⟨4214498248791569546228453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11238661996777518789942541 4214498248791569546228453)
                      ·
                        rfl

theorem cell23_8207706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_8207706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207706 prefixEnd_8207706 := by exact prefixLift 8207706
  have htrace : WordTrace (prefixWord ++ tailWord_8207706) baseStart_8207706 baseEnd_8207706 := by
    simpa [prefixWord, tailWord_8207706, baseEnd_8207706] using wordTrace_append hprefix tailTrace_8207706
  have hstable : (prefixWord ++ tailWord_8207706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207706).length < 2 ^ (prefixWord ++ tailWord_8207706).sum := by decide
  have hdescent : baseEnd_8207706 < baseStart_8207706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207747 : List Nat := [1, 1, 1, 3, 5, 2, 3, 2, 1, 4]
def baseStart_8207747 : Nat := 118140960795 + 8207747 * 2 ^ 59
def prefixEnd_8207747 : Nat := 4983230072969 + 3 ^ 40 * 8207747 * 2
def baseEnd_8207747 : Nat := 1404839767166134628605255

theorem tailTrace_8207747 : CollatzResearch.WordTrace tailWord_8207747 prefixEnd_8207747 1404839767166134628605255 := by
  unfold tailWord_8207747
  simp only [CollatzResearch.WordTrace]
  refine ⟨299361126595741865431973495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199574084397161243621315663 299361126595741865431973495)
  ·
    refine ⟨449041689893612798147960243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299361126595741865431973495 449041689893612798147960243)
    ·
      refine ⟨673562534840419197221940365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449041689893612798147960243 673562534840419197221940365)
      ·
        refine ⟨252585950565157198958227637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673562534840419197221940365 252585950565157198958227637)
        ·
          refine ⟨23679932865483487402333841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252585950565157198958227637 23679932865483487402333841)
          ·
            refine ⟨17759949649112615551750381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23679932865483487402333841 17759949649112615551750381)
            ·
              refine ⟨6659981118417230831906393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17759949649112615551750381 6659981118417230831906393)
              ·
                refine ⟨4994985838812923123929795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659981118417230831906393 4994985838812923123929795)
                ·
                  refine ⟨7492478758219384685894693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994985838812923123929795 7492478758219384685894693)
                  ·
                    refine ⟨1404839767166134628605255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492478758219384685894693 1404839767166134628605255)
                    ·
                      rfl

theorem cell23_8207747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 4].length) (baseStart_8207747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207747 prefixEnd_8207747 := by exact prefixLift 8207747
  have htrace : WordTrace (prefixWord ++ tailWord_8207747) baseStart_8207747 baseEnd_8207747 := by
    simpa [prefixWord, tailWord_8207747, baseEnd_8207747] using wordTrace_append hprefix tailTrace_8207747
  have hstable : (prefixWord ++ tailWord_8207747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207747).length < 2 ^ (prefixWord ++ tailWord_8207747).sum := by decide
  have hdescent : baseEnd_8207747 < baseStart_8207747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207756 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_8207756 : Nat := 118140960795 + 8207756 * 2 ^ 59
def prefixEnd_8207756 : Nat := 4983230072969 + 3 ^ 40 * 8207756 * 2
def baseEnd_8207756 : Nat := 1404841307608098116867741

theorem tailTrace_8207756 : CollatzResearch.WordTrace tailWord_8207756 prefixEnd_8207756 1404841307608098116867741 := by
  unfold tailWord_8207756
  simp only [CollatzResearch.WordTrace]
  refine ⟨149680727426354629984525561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199574303235139506646034081 149680727426354629984525561)
  ·
    refine ⟨112260545569765972488394171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149680727426354629984525561 112260545569765972488394171)
    ·
      refine ⟨168390818354648958732591257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112260545569765972488394171 168390818354648958732591257)
      ·
        refine ⟨126293113765986719049443443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168390818354648958732591257 126293113765986719049443443)
        ·
          refine ⟨189439670648980078574165165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126293113765986719049443443 189439670648980078574165165)
          ·
            refine ⟨71039876493367529465311937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189439670648980078574165165 71039876493367529465311937)
            ·
              refine ⟨53279907370025647098983953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71039876493367529465311937 53279907370025647098983953)
              ·
                refine ⟨39959930527519235324237965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53279907370025647098983953 39959930527519235324237965)
                ·
                  refine ⟨14984973947819713246589237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39959930527519235324237965 14984973947819713246589237)
                  ·
                    refine ⟨1404841307608098116867741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14984973947819713246589237 1404841307608098116867741)
                    ·
                      rfl

theorem cell23_8207756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_8207756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207756 prefixEnd_8207756 := by exact prefixLift 8207756
  have htrace : WordTrace (prefixWord ++ tailWord_8207756) baseStart_8207756 baseEnd_8207756 := by
    simpa [prefixWord, tailWord_8207756, baseEnd_8207756] using wordTrace_append hprefix tailTrace_8207756
  have hstable : (prefixWord ++ tailWord_8207756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207756).length < 2 ^ (prefixWord ++ tailWord_8207756).sum := by decide
  have hdescent : baseEnd_8207756 < baseStart_8207756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207759 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_8207759 : Nat := 118140960795 + 8207759 * 2 ^ 59
def prefixEnd_8207759 : Nat := 4983230072969 + 3 ^ 40 * 8207759 * 2
def baseEnd_8207759 : Nat := 4214525463266257838865709

theorem tailTrace_8207759 : CollatzResearch.WordTrace tailWord_8207759 prefixEnd_8207759 4214525463266257838865709 := by
  unfold tailWord_8207759
  simp only [CollatzResearch.WordTrace]
  refine ⟨299361564271698391481410331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199574376181132260987606887 299361564271698391481410331)
  ·
    refine ⟨449042346407547587222115497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299361564271698391481410331 449042346407547587222115497)
    ·
      refine ⟨336781759805660690416586623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449042346407547587222115497 336781759805660690416586623)
      ·
        refine ⟨505172639708491035624879935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336781759805660690416586623 505172639708491035624879935)
        ·
          refine ⟨757758959562736553437319903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505172639708491035624879935 757758959562736553437319903)
          ·
            refine ⟨1136638439344104830155979855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757758959562736553437319903 1136638439344104830155979855)
            ·
              refine ⟨1704957659016157245233969783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136638439344104830155979855 1704957659016157245233969783)
              ·
                refine ⟨2557436488524235867850954675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704957659016157245233969783 2557436488524235867850954675)
                ·
                  refine ⟨3836154732786353801776432013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557436488524235867850954675 3836154732786353801776432013)
                  ·
                    refine ⟨1438558024794882675666162005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3836154732786353801776432013 1438558024794882675666162005)
                    ·
                      refine ⟨4214525463266257838865709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1438558024794882675666162005 4214525463266257838865709)
                      ·
                        rfl

theorem cell23_8207759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_8207759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207759 prefixEnd_8207759 := by exact prefixLift 8207759
  have htrace : WordTrace (prefixWord ++ tailWord_8207759) baseStart_8207759 baseEnd_8207759 := by
    simpa [prefixWord, tailWord_8207759, baseEnd_8207759] using wordTrace_append hprefix tailTrace_8207759
  have hstable : (prefixWord ++ tailWord_8207759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207759).length < 2 ^ (prefixWord ++ tailWord_8207759).sum := by decide
  have hdescent : baseEnd_8207759 < baseStart_8207759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207773 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_8207773 : Nat := 118140960795 + 8207773 * 2 ^ 59
def prefixEnd_8207773 : Nat := 4983230072969 + 3 ^ 40 * 8207773 * 2
def baseEnd_8207773 : Nat := 1404844217331806928030215

theorem tailTrace_8207773 : CollatzResearch.WordTrace tailWord_8207773 prefixEnd_8207773 1404844217331806928030215 := by
  unfold tailWord_8207773
  simp only [CollatzResearch.WordTrace]
  refine ⟨299362074893647671872419973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199574716595765114581613315 299362074893647671872419973)
  ·
    refine ⟨56130389042558938476078745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299362074893647671872419973 56130389042558938476078745)
    ·
      refine ⟨42097791781919203857059059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56130389042558938476078745 42097791781919203857059059)
      ·
        refine ⟨63146687672878805785588589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42097791781919203857059059 63146687672878805785588589)
        ·
          refine ⟨23680007877329552169595721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63146687672878805785588589 23680007877329552169595721)
          ·
            refine ⟨17760005907997164127196791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23680007877329552169595721 17760005907997164127196791)
            ·
              refine ⟨26640008861995746190795187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17760005907997164127196791 26640008861995746190795187)
              ·
                refine ⟨39960013292993619286192781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26640008861995746190795187 39960013292993619286192781)
                ·
                  refine ⟨14985004984872607232322293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39960013292993619286192781 14985004984872607232322293)
                  ·
                    refine ⟨1404844217331806928030215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14985004984872607232322293 1404844217331806928030215)
                    ·
                      rfl

theorem cell23_8207773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_8207773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207773 prefixEnd_8207773 := by exact prefixLift 8207773
  have htrace : WordTrace (prefixWord ++ tailWord_8207773) baseStart_8207773 baseEnd_8207773 := by
    simpa [prefixWord, tailWord_8207773, baseEnd_8207773] using wordTrace_append hprefix tailTrace_8207773
  have hstable : (prefixWord ++ tailWord_8207773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207773).length < 2 ^ (prefixWord ++ tailWord_8207773).sum := by decide
  have hdescent : baseEnd_8207773 < baseStart_8207773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207804 : List Nat := [2, 2, 2, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_8207804 : Nat := 118140960795 + 8207804 * 2 ^ 59
def prefixEnd_8207804 : Nat := 4983230072969 + 3 ^ 40 * 8207804 * 2
def baseEnd_8207804 : Nat := 4214548569895710162803003

theorem tailTrace_8207804 : CollatzResearch.WordTrace tailWord_8207804 prefixEnd_8207804 4214548569895710162803003 := by
  unfold tailWord_8207804
  simp only [CollatzResearch.WordTrace]
  refine ⟨149681602778267682083399233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199575470371023576111198977 149681602778267682083399233)
  ·
    refine ⟨112261202083700761562549425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149681602778267682083399233 112261202083700761562549425)
    ·
      refine ⟨84195901562775571171912069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112261202083700761562549425 84195901562775571171912069)
      ·
        refine ⟨15786731543020419594733513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84195901562775571171912069 15786731543020419594733513)
        ·
          refine ⟨11840048657265314696050135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15786731543020419594733513 11840048657265314696050135)
          ·
            refine ⟨17760072985897972044075203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11840048657265314696050135 17760072985897972044075203)
            ·
              refine ⟨26640109478846958066112805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17760072985897972044075203 26640109478846958066112805)
              ·
                refine ⟨4995020527283804637396151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26640109478846958066112805 4995020527283804637396151)
                ·
                  refine ⟨7492530790925706956094227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995020527283804637396151 7492530790925706956094227)
                  ·
                    refine ⟨11238796186388560434141341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492530790925706956094227 11238796186388560434141341)
                    ·
                      refine ⟨4214548569895710162803003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11238796186388560434141341 4214548569895710162803003)
                      ·
                        rfl

theorem cell23_8207804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_8207804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207804 prefixEnd_8207804 := by exact prefixLift 8207804
  have htrace : WordTrace (prefixWord ++ tailWord_8207804) baseStart_8207804 baseEnd_8207804 := by
    simpa [prefixWord, tailWord_8207804, baseEnd_8207804] using wordTrace_append hprefix tailTrace_8207804
  have hstable : (prefixWord ++ tailWord_8207804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207804).length < 2 ^ (prefixWord ++ tailWord_8207804).sum := by decide
  have hdescent : baseEnd_8207804 < baseStart_8207804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207820 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_8207820 : Nat := 118140960795 + 8207820 * 2 ^ 59
def prefixEnd_8207820 : Nat := 4983230072969 + 3 ^ 40 * 8207820 * 2
def baseEnd_8207820 : Nat := 1404852261862060700067643

theorem tailTrace_8207820 : CollatzResearch.WordTrace tailWord_8207820 prefixEnd_8207820 1404852261862060700067643 := by
  unfold tailWord_8207820
  simp only [CollatzResearch.WordTrace]
  refine ⟨149681894562238699449690457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199575859416318265932920609 149681894562238699449690457)
  ·
    refine ⟨112261420921679024587267843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149681894562238699449690457 112261420921679024587267843)
    ·
      refine ⟨168392131382518536880901765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112261420921679024587267843 168392131382518536880901765)
      ·
        refine ⟨31573524634222225665169081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168392131382518536880901765 31573524634222225665169081)
        ·
          refine ⟨23680143475666669248876811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31573524634222225665169081 23680143475666669248876811)
          ·
            refine ⟨35520215213500003873315217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23680143475666669248876811 35520215213500003873315217)
            ·
              refine ⟨26640161410125002904986413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35520215213500003873315217 26640161410125002904986413)
              ·
                refine ⟨9990060528796876089369905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26640161410125002904986413 9990060528796876089369905)
                ·
                  refine ⟨7492545396597657067027429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9990060528796876089369905 7492545396597657067027429)
                  ·
                    refine ⟨1404852261862060700067643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492545396597657067027429 1404852261862060700067643)
                    ·
                      rfl

theorem cell23_8207820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_8207820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207820 prefixEnd_8207820 := by exact prefixLift 8207820
  have htrace : WordTrace (prefixWord ++ tailWord_8207820) baseStart_8207820 baseEnd_8207820 := by
    simpa [prefixWord, tailWord_8207820, baseEnd_8207820] using wordTrace_append hprefix tailTrace_8207820
  have hstable : (prefixWord ++ tailWord_8207820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207820).length < 2 ^ (prefixWord ++ tailWord_8207820).sum := by decide
  have hdescent : baseEnd_8207820 < baseStart_8207820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207833 : List Nat := [1, 2, 1, 2, 4, 3, 3, 7]
def baseStart_8207833 : Nat := 118140960795 + 8207833 * 2 ^ 59
def prefixEnd_8207833 : Nat := 4983230072969 + 3 ^ 40 * 8207833 * 2
def baseEnd_8207833 : Nat := 156094942993877427753347

theorem tailTrace_8207833 : CollatzResearch.WordTrace tailWord_8207833 prefixEnd_8207833 156094942993877427753347 := by
  unfold tailWord_8207833
  simp only [CollatzResearch.WordTrace]
  refine ⟨299364263273430302119604153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199576175515620201413069435 299364263273430302119604153)
  ·
    refine ⟨224523197455072726589703115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299364263273430302119604153 224523197455072726589703115)
    ·
      refine ⟨336784796182609089884554673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224523197455072726589703115 336784796182609089884554673)
      ·
        refine ⟨252588597136956817413416005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336784796182609089884554673 252588597136956817413416005)
        ·
          refine ⟨47360361963179403265015501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252588597136956817413416005 47360361963179403265015501)
          ·
            refine ⟨17760135736192276224380813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47360361963179403265015501 17760135736192276224380813)
            ·
              refine ⟨6660050901072103584142805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17760135736192276224380813 6660050901072103584142805)
              ·
                refine ⟨156094942993877427753347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6660050901072103584142805 156094942993877427753347)
                ·
                  rfl

theorem cell23_8207833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 7].length) (baseStart_8207833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207833 prefixEnd_8207833 := by exact prefixLift 8207833
  have htrace : WordTrace (prefixWord ++ tailWord_8207833) baseStart_8207833 baseEnd_8207833 := by
    simpa [prefixWord, tailWord_8207833, baseEnd_8207833] using wordTrace_append hprefix tailTrace_8207833
  have hstable : (prefixWord ++ tailWord_8207833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207833).length < 2 ^ (prefixWord ++ tailWord_8207833).sum := by decide
  have hdescent : baseEnd_8207833 < baseStart_8207833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207847 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_8207847 : Nat := 118140960795 + 8207847 * 2 ^ 59
def prefixEnd_8207847 : Nat := 4983230072969 + 3 ^ 40 * 8207847 * 2
def baseEnd_8207847 : Nat := 4214570649563853494565305

theorem tailTrace_8207847 : CollatzResearch.WordTrace tailWord_8207847 prefixEnd_8207847 4214570649563853494565305 := by
  unfold tailWord_8207847
  simp only [CollatzResearch.WordTrace]
  refine ⟨299364773895379582510613795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199576515930253055007075863 299364773895379582510613795)
  ·
    refine ⟨449047160843069373765920693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299364773895379582510613795 449047160843069373765920693)
    ·
      refine ⟨42098171329037753790555065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449047160843069373765920693 42098171329037753790555065)
      ·
        refine ⟨31573628496778315342916299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42098171329037753790555065 31573628496778315342916299)
        ·
          refine ⟨47360442745167473014374449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31573628496778315342916299 47360442745167473014374449)
          ·
            refine ⟨35520332058875604760780837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47360442745167473014374449 35520332058875604760780837)
            ·
              refine ⟨6660062261039175892646407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35520332058875604760780837 6660062261039175892646407)
              ·
                refine ⟨9990093391558763838969611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6660062261039175892646407 9990093391558763838969611)
                ·
                  refine ⟨14985140087338145758454417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9990093391558763838969611 14985140087338145758454417)
                  ·
                    refine ⟨11238855065503609318840813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14985140087338145758454417 11238855065503609318840813)
                    ·
                      refine ⟨4214570649563853494565305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11238855065503609318840813 4214570649563853494565305)
                      ·
                        rfl

theorem cell23_8207847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_8207847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207847 prefixEnd_8207847 := by exact prefixLift 8207847
  have htrace : WordTrace (prefixWord ++ tailWord_8207847) baseStart_8207847 baseEnd_8207847 := by
    simpa [prefixWord, tailWord_8207847, baseEnd_8207847] using wordTrace_append hprefix tailTrace_8207847
  have hstable : (prefixWord ++ tailWord_8207847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207847).length < 2 ^ (prefixWord ++ tailWord_8207847).sum := by decide
  have hdescent : baseEnd_8207847 < baseStart_8207847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207861 : List Nat := [1, 3, 5, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_8207861 : Nat := 118140960795 + 8207861 * 2 ^ 59
def prefixEnd_8207861 : Nat := 4983230072969 + 3 ^ 40 * 8207861 * 2
def baseEnd_8207861 : Nat := 4214577838293016439790241

theorem tailTrace_8207861 : CollatzResearch.WordTrace tailWord_8207861 prefixEnd_8207861 4214577838293016439790241 := by
  unfold tailWord_8207861
  simp only [CollatzResearch.WordTrace]
  refine ⟨299365284517328862901623437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199576856344885908601082291 299365284517328862901623437)
  ·
    refine ⟨112261981693998323588108789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299365284517328862901623437 112261981693998323588108789)
    ·
      refine ⟨10524560783812342836385199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112261981693998323588108789 10524560783812342836385199)
      ·
        refine ⟨15786841175718514254577799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10524560783812342836385199 15786841175718514254577799)
        ·
          refine ⟨23680261763577771381866699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15786841175718514254577799 23680261763577771381866699)
          ·
            refine ⟨35520392645366657072800049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23680261763577771381866699 35520392645366657072800049)
            ·
              refine ⟨26640294484024992804600037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35520392645366657072800049 26640294484024992804600037)
              ·
                refine ⟨4995055215754686150862507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26640294484024992804600037 4995055215754686150862507)
                ·
                  refine ⟨7492582823632029226293761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995055215754686150862507 7492582823632029226293761)
                  ·
                    refine ⟨5619437117724021919720321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7492582823632029226293761 5619437117724021919720321)
                    ·
                      refine ⟨4214577838293016439790241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619437117724021919720321 4214577838293016439790241)
                      ·
                        rfl

theorem cell23_8207861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_8207861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207861 prefixEnd_8207861 := by exact prefixLift 8207861
  have htrace : WordTrace (prefixWord ++ tailWord_8207861) baseStart_8207861 baseEnd_8207861 := by
    simpa [prefixWord, tailWord_8207861, baseEnd_8207861] using wordTrace_append hprefix tailTrace_8207861
  have hstable : (prefixWord ++ tailWord_8207861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207861).length < 2 ^ (prefixWord ++ tailWord_8207861).sum := by decide
  have hdescent : baseEnd_8207861 < baseStart_8207861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207900 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_8207900 : Nat := 118140960795 + 8207900 * 2 ^ 59
def prefixEnd_8207900 : Nat := 4983230072969 + 3 ^ 40 * 8207900 * 2
def baseEnd_8207900 : Nat := 4214597864038541787202561

theorem tailTrace_8207900 : CollatzResearch.WordTrace tailWord_8207900 prefixEnd_8207900 4214597864038541787202561 := by
  unfold tailWord_8207900
  simp only [CollatzResearch.WordTrace]
  refine ⟨149683353482093786281146577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199577804642791715041528769 149683353482093786281146577)
  ·
    refine ⟨112262515111570339710859933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149683353482093786281146577 112262515111570339710859933)
    ·
      refine ⟨42098443166838877391572475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112262515111570339710859933 42098443166838877391572475)
      ·
        refine ⟨63147664750258316087358713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42098443166838877391572475 63147664750258316087358713)
        ·
          refine ⟨47360748562693737065519035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63147664750258316087358713 47360748562693737065519035)
          ·
            refine ⟨71041122844040605598278553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47360748562693737065519035 71041122844040605598278553)
            ·
              refine ⟨53280842133030454198708915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71041122844040605598278553 53280842133030454198708915)
              ·
                refine ⟨79921263199545681298063373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53280842133030454198708915 79921263199545681298063373)
                ·
                  refine ⟨29970473699829630486773765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79921263199545681298063373 29970473699829630486773765)
                  ·
                    refine ⟨5619463818718055716270081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29970473699829630486773765 5619463818718055716270081)
                    ·
                      refine ⟨4214597864038541787202561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619463818718055716270081 4214597864038541787202561)
                      ·
                        rfl

theorem cell23_8207900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_8207900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207900 prefixEnd_8207900 := by exact prefixLift 8207900
  have htrace : WordTrace (prefixWord ++ tailWord_8207900) baseStart_8207900 baseEnd_8207900 := by
    simpa [prefixWord, tailWord_8207900, baseEnd_8207900] using wordTrace_append hprefix tailTrace_8207900
  have hstable : (prefixWord ++ tailWord_8207900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207900).length < 2 ^ (prefixWord ++ tailWord_8207900).sum := by decide
  have hdescent : baseEnd_8207900 < baseStart_8207900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8207923 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 7]
def baseStart_8207923 : Nat := 118140960795 + 8207923 * 2 ^ 59
def prefixEnd_8207923 : Nat := 4983230072969 + 3 ^ 40 * 8207923 * 2
def baseEnd_8207923 : Nat := 468289963788177244134995

theorem tailTrace_8207923 : CollatzResearch.WordTrace tailWord_8207923 prefixEnd_8207923 468289963788177244134995 := by
  unfold tailWord_8207923
  simp only [CollatzResearch.WordTrace]
  refine ⟨299367545843104247490380423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199578363895402831660253615 299367545843104247490380423)
  ·
    refine ⟨449051318764656371235570635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299367545843104247490380423 449051318764656371235570635)
    ·
      refine ⟨673576978146984556853355953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449051318764656371235570635 673576978146984556853355953)
      ·
        refine ⟨505182733610238417640016965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673576978146984556853355953 505182733610238417640016965)
        ·
          refine ⟨94721762551919703307503181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505182733610238417640016965 94721762551919703307503181)
          ·
            refine ⟨35520660956969888740313693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94721762551919703307503181 35520660956969888740313693)
            ·
              refine ⟨13320247858863708277617635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35520660956969888740313693 13320247858863708277617635)
              ·
                refine ⟨19980371788295562416426453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13320247858863708277617635 19980371788295562416426453)
                ·
                  refine ⟨468289963788177244134995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19980371788295562416426453 468289963788177244134995)
                  ·
                    rfl

theorem cell23_8207923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 7].length) (baseStart_8207923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8207923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8207923 prefixEnd_8207923 := by exact prefixLift 8207923
  have htrace : WordTrace (prefixWord ++ tailWord_8207923) baseStart_8207923 baseEnd_8207923 := by
    simpa [prefixWord, tailWord_8207923, baseEnd_8207923] using wordTrace_append hprefix tailTrace_8207923
  have hstable : (prefixWord ++ tailWord_8207923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8207923).length < 2 ^ (prefixWord ++ tailWord_8207923).sum := by decide
  have hdescent : baseEnd_8207923 < baseStart_8207923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8207923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208000 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 3, 4]
def baseStart_8208000 : Nat := 118140960795 + 8208000 * 2 ^ 59
def prefixEnd_8208000 : Nat := 4983230072969 + 3 ^ 40 * 8208000 * 2
def baseEnd_8208000 : Nat := 1404883070701330465317367

theorem tailTrace_8208000 : CollatzResearch.WordTrace tailWord_8208000 prefixEnd_8208000 1404883070701330465317367 := by
  unfold tailWord_8208000
  simp only [CollatzResearch.WordTrace]
  refine ⟨149685177131912644820466727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199580236175883526427288969 149685177131912644820466727)
  ·
    refine ⟨224527765697868967230700091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149685177131912644820466727 224527765697868967230700091)
    ·
      refine ⟨336791648546803450846050137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224527765697868967230700091 336791648546803450846050137)
      ·
        refine ⟨252593736410102588134537603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336791648546803450846050137 252593736410102588134537603)
        ·
          refine ⟨378890604615153882201806405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252593736410102588134537603 378890604615153882201806405)
          ·
            refine ⟨71041988365341352912838701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378890604615153882201806405 71041988365341352912838701)
            ·
              refine ⟨26640745637003007342314513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71041988365341352912838701 26640745637003007342314513)
              ·
                refine ⟨19980559227752255506735885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26640745637003007342314513 19980559227752255506735885)
                ·
                  refine ⟨7492709710407095815025957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19980559227752255506735885 7492709710407095815025957)
                  ·
                    refine ⟨1404883070701330465317367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492709710407095815025957 1404883070701330465317367)
                    ·
                      rfl

theorem cell23_8208000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 4].length) (baseStart_8208000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208000 prefixEnd_8208000 := by exact prefixLift 8208000
  have htrace : WordTrace (prefixWord ++ tailWord_8208000) baseStart_8208000 baseEnd_8208000 := by
    simpa [prefixWord, tailWord_8208000, baseEnd_8208000] using wordTrace_append hprefix tailTrace_8208000
  have hstable : (prefixWord ++ tailWord_8208000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208000).length < 2 ^ (prefixWord ++ tailWord_8208000).sum := by decide
  have hdescent : baseEnd_8208000 < baseStart_8208000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208004 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_8208004 : Nat := 118140960795 + 8208004 * 2 ^ 59
def prefixEnd_8208004 : Nat := 4983230072969 + 3 ^ 40 * 8208004 * 2
def baseEnd_8208004 : Nat := 1404883755342203126767361

theorem tailTrace_8208004 : CollatzResearch.WordTrace tailWord_8208004 prefixEnd_8208004 1404883755342203126767361 := by
  unfold tailWord_8208004
  simp only [CollatzResearch.WordTrace]
  refine ⟨149685250077905399162039533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199580333437207198882719377 149685250077905399162039533)
  ·
    refine ⟨56131968779214524685764825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149685250077905399162039533 56131968779214524685764825)
    ·
      refine ⟨42098976584410893514323619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56131968779214524685764825 42098976584410893514323619)
      ·
        refine ⟨63148464876616340271485429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42098976584410893514323619 63148464876616340271485429)
        ·
          refine ⟨5920168582182781900451759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63148464876616340271485429 5920168582182781900451759)
          ·
            refine ⟨8880252873274172850677639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920168582182781900451759 8880252873274172850677639)
            ·
              refine ⟨13320379309911259276016459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8880252873274172850677639 13320379309911259276016459)
              ·
                refine ⟨19980568964866888914024689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13320379309911259276016459 19980568964866888914024689)
                ·
                  refine ⟨14985426723650166685518517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19980568964866888914024689 14985426723650166685518517)
                  ·
                    refine ⟨1404883755342203126767361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14985426723650166685518517 1404883755342203126767361)
                    ·
                      rfl

theorem cell23_8208004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_8208004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208004 prefixEnd_8208004 := by exact prefixLift 8208004
  have htrace : WordTrace (prefixWord ++ tailWord_8208004) baseStart_8208004 baseEnd_8208004 := by
    simpa [prefixWord, tailWord_8208004, baseEnd_8208004] using wordTrace_append hprefix tailTrace_8208004
  have hstable : (prefixWord ++ tailWord_8208004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208004).length < 2 ^ (prefixWord ++ tailWord_8208004).sum := by decide
  have hdescent : baseEnd_8208004 < baseStart_8208004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208007 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_8208007 : Nat := 118140960795 + 8208007 * 2 ^ 59
def prefixEnd_8208007 : Nat := 4983230072969 + 3 ^ 40 * 8208007 * 2
def baseEnd_8208007 : Nat := 4214652806468572868564569

theorem tailTrace_8208007 : CollatzResearch.WordTrace tailWord_8208007 prefixEnd_8208007 4214652806468572868564569 := by
  unfold tailWord_8208007
  simp only [CollatzResearch.WordTrace]
  refine ⟨299370609574799929836438275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199580406383199953224292183 299370609574799929836438275)
  ·
    refine ⟨449055914362199894754657413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299370609574799929836438275 449055914362199894754657413)
    ·
      refine ⟨84197983942912480266498265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449055914362199894754657413 84197983942912480266498265)
      ·
        refine ⟨63148487957184360199873699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84197983942912480266498265 63148487957184360199873699)
        ·
          refine ⟨94722731935776540299810549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63148487957184360199873699 94722731935776540299810549)
          ·
            refine ⟨8880256118979050653107239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94722731935776540299810549 8880256118979050653107239)
            ·
              refine ⟨13320384178468575979660859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8880256118979050653107239 13320384178468575979660859)
              ·
                refine ⟨19980576267702863969491289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13320384178468575979660859 19980576267702863969491289)
                ·
                  refine ⟨14985432200777147977118467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19980576267702863969491289 14985432200777147977118467)
                  ·
                    refine ⟨22478148301165721965677701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14985432200777147977118467 22478148301165721965677701)
                    ·
                      refine ⟨4214652806468572868564569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22478148301165721965677701 4214652806468572868564569)
                      ·
                        rfl

theorem cell23_8208007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_8208007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208007 prefixEnd_8208007 := by exact prefixLift 8208007
  have htrace : WordTrace (prefixWord ++ tailWord_8208007) baseStart_8208007 baseEnd_8208007 := by
    simpa [prefixWord, tailWord_8208007, baseEnd_8208007] using wordTrace_append hprefix tailTrace_8208007
  have hstable : (prefixWord ++ tailWord_8208007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208007).length < 2 ^ (prefixWord ++ tailWord_8208007).sum := by decide
  have hdescent : baseEnd_8208007 < baseStart_8208007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208057 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 3]
def baseStart_8208057 : Nat := 118140960795 + 8208057 * 2 ^ 59
def prefixEnd_8208057 : Nat := 4983230072969 + 3 ^ 40 * 8208057 * 2
def baseEnd_8208057 : Nat := 4214678480501297672939339

theorem tailTrace_8208057 : CollatzResearch.WordTrace tailWord_8208057 prefixEnd_8208057 4214678480501297672939339 := by
  unfold tailWord_8208057
  simp only [CollatzResearch.WordTrace]
  refine ⟨299372433224618788375758425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199581622149745858917172283 299372433224618788375758425)
  ·
    refine ⟨224529324918464091281818819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299372433224618788375758425 224529324918464091281818819)
    ·
      refine ⟨336793987377696136922728229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224529324918464091281818819 336793987377696136922728229)
      ·
        refine ⟨63148872633318025673011543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336793987377696136922728229 63148872633318025673011543)
        ·
          refine ⟨94723308949977038509517315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63148872633318025673011543 94723308949977038509517315)
          ·
            refine ⟨142084963424965557764275973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94723308949977038509517315 142084963424965557764275973)
            ·
              refine ⟨26640930642181042080801745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142084963424965557764275973 26640930642181042080801745)
              ·
                refine ⟨19980697981635781560601309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26640930642181042080801745 19980697981635781560601309)
                ·
                  refine ⟨7492761743113418085225491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19980697981635781560601309 7492761743113418085225491)
                  ·
                    refine ⟨11239142614670127127838237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492761743113418085225491 11239142614670127127838237)
                    ·
                      refine ⟨4214678480501297672939339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239142614670127127838237 4214678480501297672939339)
                      ·
                        rfl

theorem cell23_8208057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_8208057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208057 prefixEnd_8208057 := by exact prefixLift 8208057
  have htrace : WordTrace (prefixWord ++ tailWord_8208057) baseStart_8208057 baseEnd_8208057 := by
    simpa [prefixWord, tailWord_8208057, baseEnd_8208057] using wordTrace_append hprefix tailTrace_8208057
  have hstable : (prefixWord ++ tailWord_8208057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208057).length < 2 ^ (prefixWord ++ tailWord_8208057).sum := by decide
  have hdescent : baseEnd_8208057 < baseStart_8208057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208084 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_8208084 : Nat := 118140960795 + 8208084 * 2 ^ 59
def prefixEnd_8208084 : Nat := 4983230072969 + 3 ^ 40 * 8208084 * 2
def baseEnd_8208084 : Nat := 4214692344478969067301715

theorem tailTrace_8208084 : CollatzResearch.WordTrace tailWord_8208084 prefixEnd_8208084 4214692344478969067301715 := by
  unfold tailWord_8208084
  simp only [CollatzResearch.WordTrace]
  refine ⟨149686708997760485993495653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199582278663680647991327537 149686708997760485993495653)
  ·
    refine ⟨28066257937080091123780435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149686708997760485993495653 28066257937080091123780435)
    ·
      refine ⟨42099386905620136685670653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28066257937080091123780435 42099386905620136685670653)
      ·
        refine ⟨15787270089607551257126495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42099386905620136685670653 15787270089607551257126495)
        ·
          refine ⟨23680905134411326885689743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15787270089607551257126495 23680905134411326885689743)
          ·
            refine ⟨35521357701616990328534615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23680905134411326885689743 35521357701616990328534615)
            ·
              refine ⟨53282036552425485492801923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35521357701616990328534615 53282036552425485492801923)
              ·
                refine ⟨79923054828638228239202885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53282036552425485492801923 79923054828638228239202885)
                ·
                  refine ⟨14985572780369667794850541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79923054828638228239202885 14985572780369667794850541)
                  ·
                    refine ⟨5619589792638625423068953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14985572780369667794850541 5619589792638625423068953)
                    ·
                      refine ⟨4214692344478969067301715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619589792638625423068953 4214692344478969067301715)
                      ·
                        rfl

theorem cell23_8208084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_8208084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208084 prefixEnd_8208084 := by exact prefixLift 8208084
  have htrace : WordTrace (prefixWord ++ tailWord_8208084) baseStart_8208084 baseEnd_8208084 := by
    simpa [prefixWord, tailWord_8208084, baseEnd_8208084] using wordTrace_append hprefix tailTrace_8208084
  have hstable : (prefixWord ++ tailWord_8208084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208084).length < 2 ^ (prefixWord ++ tailWord_8208084).sum := by decide
  have hdescent : baseEnd_8208084 < baseStart_8208084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208100 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_8208100 : Nat := 118140960795 + 8208100 * 2 ^ 59
def prefixEnd_8208100 : Nat := 4983230072969 + 3 ^ 40 * 8208100 * 2
def baseEnd_8208100 : Nat := 4214700560169441004701641

theorem tailTrace_8208100 : CollatzResearch.WordTrace tailWord_8208100 prefixEnd_8208100 4214700560169441004701641 := by
  unfold tailWord_8208100
  simp only [CollatzResearch.WordTrace]
  refine ⟨149687000781731503359786877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199582667708975337813049169 149687000781731503359786877)
  ·
    refine ⟨56132625293149313759920079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149687000781731503359786877 56132625293149313759920079)
    ·
      refine ⟨84198937939723970639880119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56132625293149313759920079 84198937939723970639880119)
      ·
        refine ⟨126298406909585955959820179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84198937939723970639880119 126298406909585955959820179)
        ·
          refine ⟨189447610364378933939730269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126298406909585955959820179 189447610364378933939730269)
          ·
            refine ⟨71042853886642100227398851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189447610364378933939730269 71042853886642100227398851)
            ·
              refine ⟨106564280829963150341098277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71042853886642100227398851 106564280829963150341098277)
              ·
                refine ⟨19980802655618090688955927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106564280829963150341098277 19980802655618090688955927)
                ·
                  refine ⟨29971203983427136033433891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19980802655618090688955927 29971203983427136033433891)
                  ·
                    refine ⟨44956805975140704050150837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29971203983427136033433891 44956805975140704050150837)
                    ·
                      refine ⟨4214700560169441004701641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44956805975140704050150837 4214700560169441004701641)
                      ·
                        rfl

theorem cell23_8208100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_8208100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208100 prefixEnd_8208100 := by exact prefixLift 8208100
  have htrace : WordTrace (prefixWord ++ tailWord_8208100) baseStart_8208100 baseEnd_8208100 := by
    simpa [prefixWord, tailWord_8208100, baseEnd_8208100] using wordTrace_append hprefix tailTrace_8208100
  have hstable : (prefixWord ++ tailWord_8208100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208100).length < 2 ^ (prefixWord ++ tailWord_8208100).sum := by decide
  have hdescent : baseEnd_8208100 < baseStart_8208100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208110 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_8208110 : Nat := 118140960795 + 8208110 * 2 ^ 59
def prefixEnd_8208110 : Nat := 4983230072969 + 3 ^ 40 * 8208110 * 2
def baseEnd_8208110 : Nat := 4214705694975985965576595

theorem tailTrace_8208110 : CollatzResearch.WordTrace tailWord_8208110 prefixEnd_8208110 4214705694975985965576595 := by
  unfold tailWord_8208110
  simp only [CollatzResearch.WordTrace]
  refine ⟨37421795786678347303429723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199582910862284518951625189 37421795786678347303429723)
  ·
    refine ⟨56132693680017520955144585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37421795786678347303429723 56132693680017520955144585)
    ·
      refine ⟨42099520260013140716358439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56132693680017520955144585 42099520260013140716358439)
      ·
        refine ⟨63149280390019711074537659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42099520260013140716358439 63149280390019711074537659)
        ·
          refine ⟨94723920585029566611806489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63149280390019711074537659 94723920585029566611806489)
          ·
            refine ⟨71042940438772174958854867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94723920585029566611806489 71042940438772174958854867)
            ·
              refine ⟨106564410658158262438282301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71042940438772174958854867 106564410658158262438282301)
              ·
                refine ⟨39961653996809348414355863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106564410658158262438282301 39961653996809348414355863)
                ·
                  refine ⟨59942480995214022621533795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39961653996809348414355863 59942480995214022621533795)
                  ·
                    refine ⟨89913721492821033932300693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59942480995214022621533795 89913721492821033932300693)
                    ·
                      refine ⟨4214705694975985965576595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89913721492821033932300693 4214705694975985965576595)
                      ·
                        rfl

theorem cell23_8208110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_8208110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208110 prefixEnd_8208110 := by exact prefixLift 8208110
  have htrace : WordTrace (prefixWord ++ tailWord_8208110) baseStart_8208110 baseEnd_8208110 := by
    simpa [prefixWord, tailWord_8208110, baseEnd_8208110] using wordTrace_append hprefix tailTrace_8208110
  have hstable : (prefixWord ++ tailWord_8208110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208110).length < 2 ^ (prefixWord ++ tailWord_8208110).sum := by decide
  have hdescent : baseEnd_8208110 < baseStart_8208110 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208114 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_8208114 : Nat := 118140960795 + 8208114 * 2 ^ 59
def prefixEnd_8208114 : Nat := 4983230072969 + 3 ^ 40 * 8208114 * 2
def baseEnd_8208114 : Nat := 4214707748898603949926577

theorem tailTrace_8208114 : CollatzResearch.WordTrace tailWord_8208114 prefixEnd_8208114 4214707748898603949926577 := by
  unfold tailWord_8208114
  simp only [CollatzResearch.WordTrace]
  refine ⟨74843628046353071777645849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199583008123608191407055597 74843628046353071777645849)
  ·
    refine ⟨56132721034764803833234387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74843628046353071777645849 56132721034764803833234387)
    ·
      refine ⟨84199081552147205749851581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56132721034764803833234387 84199081552147205749851581)
      ·
        refine ⟨31574655582055202156194343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84199081552147205749851581 31574655582055202156194343)
        ·
          refine ⟨47361983373082803234291515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31574655582055202156194343 47361983373082803234291515)
          ·
            refine ⟨71042975059624204851437273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47361983373082803234291515 71042975059624204851437273)
            ·
              refine ⟨53282231294718153638577955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71042975059624204851437273 53282231294718153638577955)
              ·
                refine ⟨79923346942077230457866933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53282231294718153638577955 79923346942077230457866933)
                ·
                  refine ⟨7492813775819740355425025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79923346942077230457866933 7492813775819740355425025)
                  ·
                    refine ⟨5619610331864805266568769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7492813775819740355425025 5619610331864805266568769)
                    ·
                      refine ⟨4214707748898603949926577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619610331864805266568769 4214707748898603949926577)
                      ·
                        rfl

theorem cell23_8208114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_8208114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208114 prefixEnd_8208114 := by exact prefixLift 8208114
  have htrace : WordTrace (prefixWord ++ tailWord_8208114) baseStart_8208114 baseEnd_8208114 := by
    simpa [prefixWord, tailWord_8208114, baseEnd_8208114] using wordTrace_append hprefix tailTrace_8208114
  have hstable : (prefixWord ++ tailWord_8208114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208114).length < 2 ^ (prefixWord ++ tailWord_8208114).sum := by decide
  have hdescent : baseEnd_8208114 < baseStart_8208114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208164 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_8208164 : Nat := 118140960795 + 8208164 * 2 ^ 59
def prefixEnd_8208164 : Nat := 4983230072969 + 3 ^ 40 * 8208164 * 2
def baseEnd_8208164 : Nat := 4214733422931328754301347

theorem tailTrace_8208164 : CollatzResearch.WordTrace tailWord_8208164 prefixEnd_8208164 4214733422931328754301347 := by
  unfold tailWord_8208164
  simp only [CollatzResearch.WordTrace]
  refine ⟨149688167917615572824951773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199584223890154097099935697 149688167917615572824951773)
  ·
    refine ⟨56133062969105839809356915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149688167917615572824951773 56133062969105839809356915)
    ·
      refine ⟨84199594453658759714035373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56133062969105839809356915 84199594453658759714035373)
      ·
        refine ⟨31574847920122034892763265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84199594453658759714035373 31574847920122034892763265)
        ·
          refine ⟨23681135940091526169572449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31574847920122034892763265 23681135940091526169572449)
          ·
            refine ⟨17760851955068644627179337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23681135940091526169572449 17760851955068644627179337)
            ·
              refine ⟨13320638966301483470384503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17760851955068644627179337 13320638966301483470384503)
              ·
                refine ⟨19980958449452225205576755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13320638966301483470384503 19980958449452225205576755)
                ·
                  refine ⟨29971437674178337808365133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19980958449452225205576755 29971437674178337808365133)
                  ·
                    refine ⟨11239289127816876678136925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29971437674178337808365133 11239289127816876678136925)
                    ·
                      refine ⟨4214733422931328754301347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239289127816876678136925 4214733422931328754301347)
                      ·
                        rfl

theorem cell23_8208164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_8208164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208164 prefixEnd_8208164 := by exact prefixLift 8208164
  have htrace : WordTrace (prefixWord ++ tailWord_8208164) baseStart_8208164 baseEnd_8208164 := by
    simpa [prefixWord, tailWord_8208164, baseEnd_8208164] using wordTrace_append hprefix tailTrace_8208164
  have hstable : (prefixWord ++ tailWord_8208164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208164).length < 2 ^ (prefixWord ++ tailWord_8208164).sum := by decide
  have hdescent : baseEnd_8208164 < baseStart_8208164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208185 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 1, 2, 3]
def baseStart_8208185 : Nat := 118140960795 + 8208185 * 2 ^ 59
def prefixEnd_8208185 : Nat := 4983230072969 + 3 ^ 40 * 8208185 * 2
def baseEnd_8208185 : Nat := 4214744206025073172138751

theorem tailTrace_8208185 : CollatzResearch.WordTrace tailWord_8208185 prefixEnd_8208185 4214744206025073172138751 := by
  unfold tailWord_8208185
  simp only [CollatzResearch.WordTrace]
  refine ⟨299377101768155066236418009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199584734512103377490945339 299377101768155066236418009)
  ·
    refine ⟨224532826326116299677313507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299377101768155066236418009 224532826326116299677313507)
    ·
      refine ⟨336799239489174449515970261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224532826326116299677313507 336799239489174449515970261)
      ·
        refine ⟨7893732175527526160530553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 336799239489174449515970261 7893732175527526160530553)
        ·
          refine ⟨5920299131645644620397915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7893732175527526160530553 5920299131645644620397915)
          ·
            refine ⟨8880448697468466930596873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920299131645644620397915 8880448697468466930596873)
            ·
              refine ⟨6660336523101350197947655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8880448697468466930596873 6660336523101350197947655)
              ·
                refine ⟨9990504784652025296921483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6660336523101350197947655 9990504784652025296921483)
                ·
                  refine ⟨14985757176978037945382225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9990504784652025296921483 14985757176978037945382225)
                  ·
                    refine ⟨11239317882733528459036669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14985757176978037945382225 11239317882733528459036669)
                    ·
                      refine ⟨4214744206025073172138751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239317882733528459036669 4214744206025073172138751)
                      ·
                        rfl

theorem cell23_8208185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_8208185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208185 prefixEnd_8208185 := by exact prefixLift 8208185
  have htrace : WordTrace (prefixWord ++ tailWord_8208185) baseStart_8208185 baseEnd_8208185 := by
    simpa [prefixWord, tailWord_8208185, baseEnd_8208185] using wordTrace_append hprefix tailTrace_8208185
  have hstable : (prefixWord ++ tailWord_8208185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208185).length < 2 ^ (prefixWord ++ tailWord_8208185).sum := by decide
  have hdescent : baseEnd_8208185 < baseStart_8208185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208191 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 1, 3, 2]
def baseStart_8208191 : Nat := 118140960795 + 8208191 * 2 ^ 59
def prefixEnd_8208191 : Nat := 4983230072969 + 3 ^ 40 * 8208191 * 2
def baseEnd_8208191 : Nat := 4214747286909000148663723

theorem tailTrace_8208191 : CollatzResearch.WordTrace tailWord_8208191 prefixEnd_8208191 4214747286909000148663723 := by
  unfold tailWord_8208191
  simp only [CollatzResearch.WordTrace]
  refine ⟨299377320606133329261136427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199584880404088886174090951 299377320606133329261136427)
  ·
    refine ⟨449065980909199993891704641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299377320606133329261136427 449065980909199993891704641)
    ·
      refine ⟨336799485681899995418778481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449065980909199993891704641 336799485681899995418778481)
      ·
        refine ⟨252599614261424996564083861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336799485681899995418778481 252599614261424996564083861)
        ·
          refine ⟨11840606918504296713941431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252599614261424996564083861 11840606918504296713941431)
          ·
            refine ⟨17760910377756445070912147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11840606918504296713941431 17760910377756445070912147)
            ·
              refine ⟨26641365566634667606368221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17760910377756445070912147 26641365566634667606368221)
              ·
                refine ⟨9990512087488000352388083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26641365566634667606368221 9990512087488000352388083)
                ·
                  refine ⟨14985768131232000528582125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9990512087488000352388083 14985768131232000528582125)
                  ·
                    refine ⟨5619663049212000198218297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14985768131232000528582125 5619663049212000198218297)
                    ·
                      refine ⟨4214747286909000148663723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619663049212000198218297 4214747286909000148663723)
                      ·
                        rfl

theorem cell23_8208191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_8208191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208191 prefixEnd_8208191 := by exact prefixLift 8208191
  have htrace : WordTrace (prefixWord ++ tailWord_8208191) baseStart_8208191 baseEnd_8208191 := by
    simpa [prefixWord, tailWord_8208191, baseEnd_8208191] using wordTrace_append hprefix tailTrace_8208191
  have hstable : (prefixWord ++ tailWord_8208191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208191).length < 2 ^ (prefixWord ++ tailWord_8208191).sum := by decide
  have hdescent : baseEnd_8208191 < baseStart_8208191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208198 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_8208198 : Nat := 118140960795 + 8208198 * 2 ^ 59
def prefixEnd_8208198 : Nat := 4983230072969 + 3 ^ 40 * 8208198 * 2
def baseEnd_8208198 : Nat := 4214750881273581621276191

theorem tailTrace_8208198 : CollatzResearch.WordTrace tailWord_8208198 prefixEnd_8208198 4214750881273581621276191 := by
  unfold tailWord_8208198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355549247409624045520039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199585050611405312971094165 9355549247409624045520039)
  ·
    refine ⟨14033323871114436068280059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9355549247409624045520039 14033323871114436068280059)
    ·
      refine ⟨21049985806671654102420089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14033323871114436068280059 21049985806671654102420089)
      ·
        refine ⟨15787489355003740576815067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21049985806671654102420089 15787489355003740576815067)
        ·
          refine ⟨23681234032505610865222601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15787489355003740576815067 23681234032505610865222601)
          ·
            refine ⟨17760925524379208148916951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23681234032505610865222601 17760925524379208148916951)
            ·
              refine ⟨26641388286568812223375427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17760925524379208148916951 26641388286568812223375427)
              ·
                refine ⟨39962082429853218335063141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26641388286568812223375427 39962082429853218335063141)
                ·
                  refine ⟨7492890455597478437824339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39962082429853218335063141 7492890455597478437824339)
                  ·
                    refine ⟨11239335683396217656736509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492890455597478437824339 11239335683396217656736509)
                    ·
                      refine ⟨4214750881273581621276191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239335683396217656736509 4214750881273581621276191)
                      ·
                        rfl

theorem cell23_8208198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_8208198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208198 prefixEnd_8208198 := by exact prefixLift 8208198
  have htrace : WordTrace (prefixWord ++ tailWord_8208198) baseStart_8208198 baseEnd_8208198 := by
    simpa [prefixWord, tailWord_8208198, baseEnd_8208198] using wordTrace_append hprefix tailTrace_8208198
  have hstable : (prefixWord ++ tailWord_8208198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208198).length < 2 ^ (prefixWord ++ tailWord_8208198).sum := by decide
  have hdescent : baseEnd_8208198 < baseStart_8208198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208237 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_8208237 : Nat := 118140960795 + 8208237 * 2 ^ 59
def prefixEnd_8208237 : Nat := 4983230072969 + 3 ^ 40 * 8208237 * 2
def baseEnd_8208237 : Nat := 4214770907019106968688511

theorem tailTrace_8208237 : CollatzResearch.WordTrace tailWord_8208237 prefixEnd_8208237 4214770907019106968688511 := by
  unfold tailWord_8208237
  simp only [CollatzResearch.WordTrace]
  refine ⟨299378998363966679117310965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199585998909311119411540643 299378998363966679117310965)
  ·
    refine ⟨28066781096621876167247903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299378998363966679117310965 28066781096621876167247903)
    ·
      refine ⟨42100171644932814250871855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28066781096621876167247903 42100171644932814250871855)
      ·
        refine ⟨63150257467399221376307783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42100171644932814250871855 63150257467399221376307783)
        ·
          refine ⟨94725386201098832064461675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63150257467399221376307783 94725386201098832064461675)
          ·
            refine ⟨142088079301648248096692513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94725386201098832064461675 142088079301648248096692513)
            ·
              refine ⟨106566059476236186072519385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142088079301648248096692513 106566059476236186072519385)
              ·
                refine ⟨79924544607177139554389539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106566059476236186072519385 79924544607177139554389539)
                ·
                  refine ⟨119886816910765709331584309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79924544607177139554389539 119886816910765709331584309)
                  ·
                    refine ⟨11239389085384285249836029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119886816910765709331584309 11239389085384285249836029)
                    ·
                      refine ⟨4214770907019106968688511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239389085384285249836029 4214770907019106968688511)
                      ·
                        rfl

theorem cell23_8208237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_8208237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208237 prefixEnd_8208237 := by exact prefixLift 8208237
  have htrace : WordTrace (prefixWord ++ tailWord_8208237) baseStart_8208237 baseEnd_8208237 := by
    simpa [prefixWord, tailWord_8208237, baseEnd_8208237] using wordTrace_append hprefix tailTrace_8208237
  have hstable : (prefixWord ++ tailWord_8208237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208237).length < 2 ^ (prefixWord ++ tailWord_8208237).sum := by decide
  have hdescent : baseEnd_8208237 < baseStart_8208237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208247 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 3, 7, 2]
def baseStart_8208247 : Nat := 118140960795 + 8208247 * 2 ^ 59
def prefixEnd_8208247 : Nat := 4983230072969 + 3 ^ 40 * 8208247 * 2
def baseEnd_8208247 : Nat := 4214776041825651929563465

theorem tailTrace_8208247 : CollatzResearch.WordTrace tailWord_8208247 prefixEnd_8208247 4214776041825651929563465 := by
  unfold tailWord_8208247
  simp only [CollatzResearch.WordTrace]
  refine ⟨299379363093930450825174995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199586242062620300550116663 299379363093930450825174995)
  ·
    refine ⟨449069044640895676237762493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299379363093930450825174995 449069044640895676237762493)
    ·
      refine ⟨168400891740335878589160935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449069044640895676237762493 168400891740335878589160935)
      ·
        refine ⟨252601337610503817883741403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168400891740335878589160935 252601337610503817883741403)
        ·
          refine ⟨378902006415755726825612105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252601337610503817883741403 378902006415755726825612105)
          ·
            refine ⟨284176504811816795119209079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378902006415755726825612105 284176504811816795119209079)
            ·
              refine ⟨426264757217725192678813619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284176504811816795119209079 426264757217725192678813619)
              ·
                refine ⟨639397135826587789018220429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426264757217725192678813619 639397135826587789018220429)
                ·
                  refine ⟨239773925934970420881832661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639397135826587789018220429 239773925934970420881832661)
                  ·
                    refine ⟨5619701389100869239417953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 239773925934970420881832661 5619701389100869239417953)
                    ·
                      refine ⟨4214776041825651929563465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619701389100869239417953 4214776041825651929563465)
                      ·
                        rfl

theorem cell23_8208247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_8208247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208247 prefixEnd_8208247 := by exact prefixLift 8208247
  have htrace : WordTrace (prefixWord ++ tailWord_8208247) baseStart_8208247 baseEnd_8208247 := by
    simpa [prefixWord, tailWord_8208247, baseEnd_8208247] using wordTrace_append hprefix tailTrace_8208247
  have hstable : (prefixWord ++ tailWord_8208247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208247).length < 2 ^ (prefixWord ++ tailWord_8208247).sum := by decide
  have hdescent : baseEnd_8208247 < baseStart_8208247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208277 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_8208277 : Nat := 118140960795 + 8208277 * 2 ^ 59
def prefixEnd_8208277 : Nat := 4983230072969 + 3 ^ 40 * 8208277 * 2
def baseEnd_8208277 : Nat := 4214791446245286812188327

theorem tailTrace_8208277 : CollatzResearch.WordTrace tailWord_8208277 prefixEnd_8208277 4214791446245286812188327 := by
  unfold tailWord_8208277
  simp only [CollatzResearch.WordTrace]
  refine ⟨299380457283821765948767085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199586971522547843965844723 299380457283821765948767085)
  ·
    refine ⟨112267671481433162230787657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299380457283821765948767085 112267671481433162230787657)
    ·
      refine ⟨84200753611074871673090743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112267671481433162230787657 84200753611074871673090743)
      ·
        refine ⟨126301130416612307509636115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84200753611074871673090743 126301130416612307509636115)
        ·
          refine ⟨189451695624918461264454173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126301130416612307509636115 189451695624918461264454173)
          ·
            refine ⟨71044385859344422974170315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189451695624918461264454173 71044385859344422974170315)
            ·
              refine ⟨106566578789016634461255473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71044385859344422974170315 106566578789016634461255473)
              ·
                refine ⟨79924934091762475845941605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106566578789016634461255473 79924934091762475845941605)
                ·
                  refine ⟨14985925142205464221114051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79924934091762475845941605 14985925142205464221114051)
                  ·
                    refine ⟨22478887713308196331671077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14985925142205464221114051 22478887713308196331671077)
                    ·
                      refine ⟨4214791446245286812188327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22478887713308196331671077 4214791446245286812188327)
                      ·
                        rfl

theorem cell23_8208277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_8208277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208277 prefixEnd_8208277 := by exact prefixLift 8208277
  have htrace : WordTrace (prefixWord ++ tailWord_8208277) baseStart_8208277 baseEnd_8208277 := by
    simpa [prefixWord, tailWord_8208277, baseEnd_8208277] using wordTrace_append hprefix tailTrace_8208277
  have hstable : (prefixWord ++ tailWord_8208277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208277).length < 2 ^ (prefixWord ++ tailWord_8208277).sum := by decide
  have hdescent : baseEnd_8208277 < baseStart_8208277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208327 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_8208327 : Nat := 118140960795 + 8208327 * 2 ^ 59
def prefixEnd_8208327 : Nat := 4983230072969 + 3 ^ 40 * 8208327 * 2
def baseEnd_8208327 : Nat := 4214817120278011616563097

theorem tailTrace_8208327 : CollatzResearch.WordTrace tailWord_8208327 prefixEnd_8208327 4214817120278011616563097 := by
  unfold tailWord_8208327
  simp only [CollatzResearch.WordTrace]
  refine ⟨299382280933640624488087235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199588187289093749658724823 299382280933640624488087235)
  ·
    refine ⟨449073421400460936732130853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299382280933640624488087235 449073421400460936732130853)
    ·
      refine ⟨84201266512586425637274535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449073421400460936732130853 84201266512586425637274535)
      ·
        refine ⟨126301899768879638455911803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84201266512586425637274535 126301899768879638455911803)
        ·
          refine ⟨189452849653319457683867705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126301899768879638455911803 189452849653319457683867705)
          ·
            refine ⟨142089637239989593262900779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189452849653319457683867705 142089637239989593262900779)
            ·
              refine ⟨213134455859984389894351169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142089637239989593262900779 213134455859984389894351169)
              ·
                refine ⟨159850841894988292420763377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213134455859984389894351169 159850841894988292420763377)
                ·
                  refine ⟨119888131421241219315572533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159850841894988292420763377 119888131421241219315572533)
                  ·
                    refine ⟨11239512320741364310834925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119888131421241219315572533 11239512320741364310834925)
                    ·
                      refine ⟨4214817120278011616563097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239512320741364310834925 4214817120278011616563097)
                      ·
                        rfl

theorem cell23_8208327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_8208327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208327 prefixEnd_8208327 := by exact prefixLift 8208327
  have htrace : WordTrace (prefixWord ++ tailWord_8208327) baseStart_8208327 baseEnd_8208327 := by
    simpa [prefixWord, tailWord_8208327, baseEnd_8208327] using wordTrace_append hprefix tailTrace_8208327
  have hstable : (prefixWord ++ tailWord_8208327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208327).length < 2 ^ (prefixWord ++ tailWord_8208327).sum := by decide
  have hdescent : baseEnd_8208327 < baseStart_8208327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208421 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_8208421 : Nat := 118140960795 + 8208421 * 2 ^ 59
def prefixEnd_8208421 : Nat := 4983230072969 + 3 ^ 40 * 8208421 * 2
def baseEnd_8208421 : Nat := 4214865387459534248787665

theorem tailTrace_8208421 : CollatzResearch.WordTrace tailWord_8208421 prefixEnd_8208421 4214865387459534248787665 := by
  unfold tailWord_8208421
  simp only [CollatzResearch.WordTrace]
  refine ⟨299385709395300078542009117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199590472930200052361339411 299385709395300078542009117)
  ·
    refine ⟨112269641023237529453253419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299385709395300078542009117 112269641023237529453253419)
    ·
      refine ⟨168404461534856294179880129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112269641023237529453253419 168404461534856294179880129)
      ·
        refine ⟨126303346151142220634910097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168404461534856294179880129 126303346151142220634910097)
        ·
          refine ⟨94727509613356665476182573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126303346151142220634910097 94727509613356665476182573)
          ·
            refine ⟨35522816105008749553568465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94727509613356665476182573 35522816105008749553568465)
            ·
              refine ⟨26642112078756562165176349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35522816105008749553568465 26642112078756562165176349)
              ·
                refine ⟨9990792029533710811941131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26642112078756562165176349 9990792029533710811941131)
                ·
                  refine ⟨14986188044300566217911697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9990792029533710811941131 14986188044300566217911697)
                  ·
                    refine ⟨11239641033225424663433773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14986188044300566217911697 11239641033225424663433773)
                    ·
                      refine ⟨4214865387459534248787665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239641033225424663433773 4214865387459534248787665)
                      ·
                        rfl

theorem cell23_8208421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_8208421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208421 prefixEnd_8208421 := by exact prefixLift 8208421
  have htrace : WordTrace (prefixWord ++ tailWord_8208421) baseStart_8208421 baseEnd_8208421 := by
    simpa [prefixWord, tailWord_8208421, baseEnd_8208421] using wordTrace_append hprefix tailTrace_8208421
  have hstable : (prefixWord ++ tailWord_8208421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208421).length < 2 ^ (prefixWord ++ tailWord_8208421).sum := by decide
  have hdescent : baseEnd_8208421 < baseStart_8208421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208508 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_8208508 : Nat := 118140960795 + 8208508 * 2 ^ 59
def prefixEnd_8208508 : Nat := 4983230072969 + 3 ^ 40 * 8208508 * 2
def baseEnd_8208508 : Nat := 4214910060276475408399765

theorem tailTrace_8208508 : CollatzResearch.WordTrace tailWord_8208508 prefixEnd_8208508 4214910060276475408399765 := by
  unfold tailWord_8208508
  simp only [CollatzResearch.WordTrace]
  refine ⟨149694441272992446200213089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199592588363989928266950785 149694441272992446200213089)
  ·
    refine ⟨112270830954744334650159817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149694441272992446200213089 112270830954744334650159817)
    ·
      refine ⟨84203123216058250987619863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112270830954744334650159817 84203123216058250987619863)
      ·
        refine ⟨126304684824087376481429795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84203123216058250987619863 126304684824087376481429795)
        ·
          refine ⟨189457027236131064722144693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126304684824087376481429795 189457027236131064722144693)
          ·
            refine ⟨17761596303387287317701065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189457027236131064722144693 17761596303387287317701065)
            ·
              refine ⟨13321197227540465488275799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17761596303387287317701065 13321197227540465488275799)
              ·
                refine ⟨19981795841310698232413699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13321197227540465488275799 19981795841310698232413699)
                ·
                  refine ⟨29972693761966047348620549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19981795841310698232413699 29972693761966047348620549)
                  ·
                    refine ⟨5619880080368633877866353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29972693761966047348620549 5619880080368633877866353)
                    ·
                      refine ⟨4214910060276475408399765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619880080368633877866353 4214910060276475408399765)
                      ·
                        rfl

theorem cell23_8208508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_8208508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208508 prefixEnd_8208508 := by exact prefixLift 8208508
  have htrace : WordTrace (prefixWord ++ tailWord_8208508) baseStart_8208508 baseEnd_8208508 := by
    simpa [prefixWord, tailWord_8208508, baseEnd_8208508] using wordTrace_append hprefix tailTrace_8208508
  have hstable : (prefixWord ++ tailWord_8208508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208508).length < 2 ^ (prefixWord ++ tailWord_8208508).sum := by decide
  have hdescent : baseEnd_8208508 < baseStart_8208508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208541 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_8208541 : Nat := 118140960795 + 8208541 * 2 ^ 59
def prefixEnd_8208541 : Nat := 4983230072969 + 3 ^ 40 * 8208541 * 2
def baseEnd_8208541 : Nat := 4214927005138073779287113

theorem tailTrace_8208541 : CollatzResearch.WordTrace tailWord_8208541 prefixEnd_8208541 4214927005138073779287113 := by
  unfold tailWord_8208541
  simp only [CollatzResearch.WordTrace]
  refine ⟨299390086154865339036377477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199593390769910226024251651 299390086154865339036377477)
  ·
    refine ⟨56135641154037251069320777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299390086154865339036377477 56135641154037251069320777)
    ·
      refine ⟨42101730865527938301990583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56135641154037251069320777 42101730865527938301990583)
      ·
        refine ⟨63152596298291907452985875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42101730865527938301990583 63152596298291907452985875)
        ·
          refine ⟨94728894447437861179478813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63152596298291907452985875 94728894447437861179478813)
          ·
            refine ⟨35523335417789197942304555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94728894447437861179478813 35523335417789197942304555)
            ·
              refine ⟨53285003126683796913456833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35523335417789197942304555 53285003126683796913456833)
              ·
                refine ⟨39963752345012847685092625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53285003126683796913456833 39963752345012847685092625)
                ·
                  refine ⟨29972814258759635763819469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39963752345012847685092625 29972814258759635763819469)
                  ·
                    refine ⟨11239805347034863411432301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29972814258759635763819469 11239805347034863411432301)
                    ·
                      refine ⟨4214927005138073779287113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239805347034863411432301 4214927005138073779287113)
                      ·
                        rfl

theorem cell23_8208541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_8208541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208541 prefixEnd_8208541 := by exact prefixLift 8208541
  have htrace : WordTrace (prefixWord ++ tailWord_8208541) baseStart_8208541 baseEnd_8208541 := by
    simpa [prefixWord, tailWord_8208541, baseEnd_8208541] using wordTrace_append hprefix tailTrace_8208541
  have hstable : (prefixWord ++ tailWord_8208541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208541).length < 2 ^ (prefixWord ++ tailWord_8208541).sum := by decide
  have hdescent : baseEnd_8208541 < baseStart_8208541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208542 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_8208542 : Nat := 118140960795 + 8208542 * 2 ^ 59
def prefixEnd_8208542 : Nat := 4983230072969 + 3 ^ 40 * 8208542 * 2
def baseEnd_8208542 : Nat := 4214927518618728275374609

theorem tailTrace_8208542 : CollatzResearch.WordTrace tailWord_8208542 prefixEnd_8208542 4214927518618728275374609 := by
  unfold tailWord_8208542
  simp only [CollatzResearch.WordTrace]
  refine ⟨37423765328482714525895485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199593415085241144138109253 37423765328482714525895485)
  ·
    refine ⟨14033911998181017947210807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37423765328482714525895485 14033911998181017947210807)
    ·
      refine ⟨21050867997271526920816211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14033911998181017947210807 21050867997271526920816211)
      ·
        refine ⟨31576301995907290381224317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21050867997271526920816211 31576301995907290381224317)
        ·
          refine ⟨11841113248465233892959119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31576301995907290381224317 11841113248465233892959119)
          ·
            refine ⟨17761669872697850839438679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11841113248465233892959119 17761669872697850839438679)
            ·
              refine ⟨26642504809046776259158019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17761669872697850839438679 26642504809046776259158019)
              ·
                refine ⟨39963757213570164388737029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26642504809046776259158019 39963757213570164388737029)
                ·
                  refine ⟨7493204477544405822888193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39963757213570164388737029 7493204477544405822888193)
                  ·
                    refine ⟨5619903358158304367166145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7493204477544405822888193 5619903358158304367166145)
                    ·
                      refine ⟨4214927518618728275374609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619903358158304367166145 4214927518618728275374609)
                      ·
                        rfl

theorem cell23_8208542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_8208542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208542 prefixEnd_8208542 := by exact prefixLift 8208542
  have htrace : WordTrace (prefixWord ++ tailWord_8208542) baseStart_8208542 baseEnd_8208542 := by
    simpa [prefixWord, tailWord_8208542, baseEnd_8208542] using wordTrace_append hprefix tailTrace_8208542
  have hstable : (prefixWord ++ tailWord_8208542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208542).length < 2 ^ (prefixWord ++ tailWord_8208542).sum := by decide
  have hdescent : baseEnd_8208542 < baseStart_8208542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208581 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 1, 6, 2]
def baseStart_8208581 : Nat := 118140960795 + 8208581 * 2 ^ 59
def prefixEnd_8208581 : Nat := 4983230072969 + 3 ^ 40 * 8208581 * 2
def baseEnd_8208581 : Nat := 4214947544364253622786929

theorem tailTrace_8208581 : CollatzResearch.WordTrace tailWord_8208581 prefixEnd_8208581 4214947544364253622786929 := by
  unfold tailWord_8208581
  simp only [CollatzResearch.WordTrace]
  refine ⟨299391545074720425867833597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199594363383146950578555731 299391545074720425867833597)
  ·
    refine ⟨112271829403020159700437599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299391545074720425867833597 112271829403020159700437599)
    ·
      refine ⟨168407744104530239550656399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112271829403020159700437599 168407744104530239550656399)
      ·
        refine ⟨252611616156795359325984599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168407744104530239550656399 252611616156795359325984599)
        ·
          refine ⟨378917424235193038988976899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252611616156795359325984599 378917424235193038988976899)
          ·
            refine ⟨568376136352789558483465349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378917424235193038988976899 568376136352789558483465349)
            ·
              refine ⟨106570525566148042215649753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 568376136352789558483465349 106570525566148042215649753)
              ·
                refine ⟨79927894174611031661737315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106570525566148042215649753 79927894174611031661737315)
                ·
                  refine ⟨119891841261916547492605973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79927894174611031661737315 119891841261916547492605973)
                  ·
                    refine ⟨5619930059152338163715905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119891841261916547492605973 5619930059152338163715905)
                    ·
                      refine ⟨4214947544364253622786929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619930059152338163715905 4214947544364253622786929)
                      ·
                        rfl

theorem cell23_8208581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_8208581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208581 prefixEnd_8208581 := by exact prefixLift 8208581
  have htrace : WordTrace (prefixWord ++ tailWord_8208581) baseStart_8208581 baseEnd_8208581 := by
    simpa [prefixWord, tailWord_8208581, baseEnd_8208581] using wordTrace_append hprefix tailTrace_8208581
  have hstable : (prefixWord ++ tailWord_8208581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208581).length < 2 ^ (prefixWord ++ tailWord_8208581).sum := by decide
  have hdescent : baseEnd_8208581 < baseStart_8208581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208584 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_8208584 : Nat := 118140960795 + 8208584 * 2 ^ 59
def prefixEnd_8208584 : Nat := 4983230072969 + 3 ^ 40 * 8208584 * 2
def baseEnd_8208584 : Nat := 4214949084806217111049415

theorem tailTrace_8208584 : CollatzResearch.WordTrace tailWord_8208584 prefixEnd_8208584 4214949084806217111049415 := by
  unfold tailWord_8208584
  simp only [CollatzResearch.WordTrace]
  refine ⟨149695827246854778690096403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199594436329139704920128537 149695827246854778690096403)
  ·
    refine ⟨224543740870282168035144605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149695827246854778690096403 224543740870282168035144605)
    ·
      refine ⟨84203902826355813013179227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224543740870282168035144605 84203902826355813013179227)
      ·
        refine ⟨126305854239533719519768841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84203902826355813013179227 126305854239533719519768841)
        ·
          refine ⟨94729390679650289639826631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126305854239533719519768841 94729390679650289639826631)
          ·
            refine ⟨142094086019475434459739947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94729390679650289639826631 142094086019475434459739947)
            ·
              refine ⟨213141129029213151689609921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142094086019475434459739947 213141129029213151689609921)
              ·
                refine ⟨159855846771909863767207441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213141129029213151689609921 159855846771909863767207441)
                ·
                  refine ⟨119891885078932397825405581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159855846771909863767207441 119891885078932397825405581)
                  ·
                    refine ⟨44959456904599649184527093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119891885078932397825405581 44959456904599649184527093)
                    ·
                      refine ⟨4214949084806217111049415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44959456904599649184527093 4214949084806217111049415)
                      ·
                        rfl

theorem cell23_8208584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_8208584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208584 prefixEnd_8208584 := by exact prefixLift 8208584
  have htrace : WordTrace (prefixWord ++ tailWord_8208584) baseStart_8208584 baseEnd_8208584 := by
    simpa [prefixWord, tailWord_8208584, baseEnd_8208584] using wordTrace_append hprefix tailTrace_8208584
  have hstable : (prefixWord ++ tailWord_8208584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208584).length < 2 ^ (prefixWord ++ tailWord_8208584).sum := by decide
  have hdescent : baseEnd_8208584 < baseStart_8208584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208601 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 3]
def baseStart_8208601 : Nat := 118140960795 + 8208601 * 2 ^ 59
def prefixEnd_8208601 : Nat := 4983230072969 + 3 ^ 40 * 8208601 * 2
def baseEnd_8208601 : Nat := 4214957813977343544536837

theorem tailTrace_8208601 : CollatzResearch.WordTrace tailWord_8208601 prefixEnd_8208601 4214957813977343544536837 := by
  unfold tailWord_8208601
  simp only [CollatzResearch.WordTrace]
  refine ⟨299392274534647969283561657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199594849689765312855707771 299392274534647969283561657)
  ·
    refine ⟨224544205900985976962671243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299392274534647969283561657 224544205900985976962671243)
    ·
      refine ⟨336816308851478965444006865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224544205900985976962671243 336816308851478965444006865)
      ·
        refine ⟨252612231638609224083005149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336816308851478965444006865 252612231638609224083005149)
        ·
          refine ⟨94729586864478459031126931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252612231638609224083005149 94729586864478459031126931)
          ·
            refine ⟨142094380296717688546690397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94729586864478459031126931 142094380296717688546690397)
            ·
              refine ⟨53285392611269133205008899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142094380296717688546690397 53285392611269133205008899)
              ·
                refine ⟨79928088916903699807513349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53285392611269133205008899 79928088916903699807513349)
                ·
                  refine ⟨14986516671919443713908753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79928088916903699807513349 14986516671919443713908753)
                  ·
                    refine ⟨11239887503939582785431565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14986516671919443713908753 11239887503939582785431565)
                    ·
                      refine ⟨4214957813977343544536837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239887503939582785431565 4214957813977343544536837)
                      ·
                        rfl

theorem cell23_8208601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_8208601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208601 prefixEnd_8208601 := by exact prefixLift 8208601
  have htrace : WordTrace (prefixWord ++ tailWord_8208601) baseStart_8208601 baseEnd_8208601 := by
    simpa [prefixWord, tailWord_8208601, baseEnd_8208601] using wordTrace_append hprefix tailTrace_8208601
  have hstable : (prefixWord ++ tailWord_8208601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208601).length < 2 ^ (prefixWord ++ tailWord_8208601).sum := by decide
  have hdescent : baseEnd_8208601 < baseStart_8208601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208610 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_8208610 : Nat := 118140960795 + 8208610 * 2 ^ 59
def prefixEnd_8208610 : Nat := 4983230072969 + 3 ^ 40 * 8208610 * 2
def baseEnd_8208610 : Nat := 4214962435303234009324297

theorem tailTrace_8208610 : CollatzResearch.WordTrace tailWord_8208610 prefixEnd_8208610 4214962435303234009324297 := by
  unfold tailWord_8208610
  simp only [CollatzResearch.WordTrace]
  refine ⟨74848150697903840955159821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199595068527743575880426189 74848150697903840955159821)
  ·
    refine ⟨28068056511713940358184933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74848150697903840955159821 28068056511713940358184933)
    ·
      refine ⟨5262760595946363817159675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28068056511713940358184933 5262760595946363817159675)
      ·
        refine ⟨7894140893919545725739513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262760595946363817159675 7894140893919545725739513)
        ·
          refine ⟨5920605670439659294304635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7894140893919545725739513 5920605670439659294304635)
          ·
            refine ⟨8880908505659488941456953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920605670439659294304635 8880908505659488941456953)
            ·
              refine ⟨6660681379244616706092715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8880908505659488941456953 6660681379244616706092715)
              ·
                refine ⟨9991022068866925059139073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6660681379244616706092715 9991022068866925059139073)
                ·
                  refine ⟨7493266551650193794354305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9991022068866925059139073 7493266551650193794354305)
                  ·
                    refine ⟨5619949913737645345765729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7493266551650193794354305 5619949913737645345765729)
                    ·
                      refine ⟨4214962435303234009324297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5619949913737645345765729 4214962435303234009324297)
                      ·
                        rfl

theorem cell23_8208610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_8208610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208610 prefixEnd_8208610 := by exact prefixLift 8208610
  have htrace : WordTrace (prefixWord ++ tailWord_8208610) baseStart_8208610 baseEnd_8208610 := by
    simpa [prefixWord, tailWord_8208610, baseEnd_8208610] using wordTrace_append hprefix tailTrace_8208610
  have hstable : (prefixWord ++ tailWord_8208610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208610).length < 2 ^ (prefixWord ++ tailWord_8208610).sum := by decide
  have hdescent : baseEnd_8208610 < baseStart_8208610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208624 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_8208624 : Nat := 118140960795 + 8208624 * 2 ^ 59
def prefixEnd_8208624 : Nat := 4983230072969 + 3 ^ 40 * 8208624 * 2
def baseEnd_8208624 : Nat := 4214969624032396954549231

theorem tailTrace_8208624 : CollatzResearch.WordTrace tailWord_8208624 prefixEnd_8208624 4214969624032396954549231 := by
  unfold tailWord_8208624
  simp only [CollatzResearch.WordTrace]
  refine ⟨149696556706782322105824463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199595408942376429474432617 149696556706782322105824463)
  ·
    refine ⟨224544835060173483158736695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149696556706782322105824463 224544835060173483158736695)
    ·
      refine ⟨336817252590260224738105043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224544835060173483158736695 336817252590260224738105043)
      ·
        refine ⟨505225878885390337107157565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336817252590260224738105043 505225878885390337107157565)
        ·
          refine ⟨189459704582021376415184087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505225878885390337107157565 189459704582021376415184087)
          ·
            refine ⟨284189556873032064622776131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189459704582021376415184087 284189556873032064622776131)
            ·
              refine ⟨426284335309548096934164197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284189556873032064622776131 426284335309548096934164197)
              ·
                refine ⟨79928312870540268175155787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426284335309548096934164197 79928312870540268175155787)
                ·
                  refine ⟨119892469305810402262733681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79928312870540268175155787 119892469305810402262733681)
                  ·
                    refine ⟨89919351979357801697050261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119892469305810402262733681 89919351979357801697050261)
                    ·
                      refine ⟨4214969624032396954549231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89919351979357801697050261 4214969624032396954549231)
                      ·
                        rfl

theorem cell23_8208624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_8208624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208624 prefixEnd_8208624 := by exact prefixLift 8208624
  have htrace : WordTrace (prefixWord ++ tailWord_8208624) baseStart_8208624 baseEnd_8208624 := by
    simpa [prefixWord, tailWord_8208624, baseEnd_8208624] using wordTrace_append hprefix tailTrace_8208624
  have hstable : (prefixWord ++ tailWord_8208624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208624).length < 2 ^ (prefixWord ++ tailWord_8208624).sum := by decide
  have hdescent : baseEnd_8208624 < baseStart_8208624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208682 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_8208682 : Nat := 118140960795 + 8208682 * 2 ^ 59
def prefixEnd_8208682 : Nat := 4983230072969 + 3 ^ 40 * 8208682 * 2
def baseEnd_8208682 : Nat := 4214999405910357727623965

theorem tailTrace_8208682 : CollatzResearch.WordTrace tailWord_8208682 prefixEnd_8208682 4214999405910357727623965 := by
  unfold tailWord_8208682
  simp only [CollatzResearch.WordTrace]
  refine ⟨74848807211838630029315075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199596819231569680078173533 74848807211838630029315075)
  ·
    refine ⟨112273210817757945043972613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74848807211838630029315075 112273210817757945043972613)
    ·
      refine ⟨21051227028329614695744865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112273210817757945043972613 21051227028329614695744865)
      ·
        refine ⟨15788420271247211021808649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21051227028329614695744865 15788420271247211021808649)
        ·
          refine ⟨11841315203435408266356487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15788420271247211021808649 11841315203435408266356487)
          ·
            refine ⟨17761972805153112399534731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11841315203435408266356487 17761972805153112399534731)
            ·
              refine ⟨26642959207729668599302097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17761972805153112399534731 26642959207729668599302097)
              ·
                refine ⟨19982219405797251449476573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26642959207729668599302097 19982219405797251449476573)
                ·
                  refine ⟨7493332277173969293553715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19982219405797251449476573 7493332277173969293553715)
                  ·
                    refine ⟨11239998415760953940330573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7493332277173969293553715 11239998415760953940330573)
                    ·
                      refine ⟨4214999405910357727623965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11239998415760953940330573 4214999405910357727623965)
                      ·
                        rfl

theorem cell23_8208682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_8208682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208682 prefixEnd_8208682 := by exact prefixLift 8208682
  have htrace : WordTrace (prefixWord ++ tailWord_8208682) baseStart_8208682 baseEnd_8208682 := by
    simpa [prefixWord, tailWord_8208682, baseEnd_8208682] using wordTrace_append hprefix tailTrace_8208682
  have hstable : (prefixWord ++ tailWord_8208682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208682).length < 2 ^ (prefixWord ++ tailWord_8208682).sum := by decide
  have hdescent : baseEnd_8208682 < baseStart_8208682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208692 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_8208692 : Nat := 118140960795 + 8208692 * 2 ^ 59
def prefixEnd_8208692 : Nat := 4983230072969 + 3 ^ 40 * 8208692 * 2
def baseEnd_8208692 : Nat := 4215004540716902688498919

theorem tailTrace_8208692 : CollatzResearch.WordTrace tailWord_8208692 prefixEnd_8208692 4215004540716902688498919 := by
  unfold tailWord_8208692
  simp only [CollatzResearch.WordTrace]
  refine ⟨149697796788659145912562165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199597062384878861216749553 149697796788659145912562165)
  ·
    refine ⟨14034168448936794929302703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149697796788659145912562165 14034168448936794929302703)
    ·
      refine ⟨21051252673405192393954055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14034168448936794929302703 21051252673405192393954055)
      ·
        refine ⟨31576879010107788590931083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21051252673405192393954055 31576879010107788590931083)
        ·
          refine ⟨47365318515161682886396625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31576879010107788590931083 47365318515161682886396625)
          ·
            refine ⟨35523988886371262164797469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47365318515161682886396625 35523988886371262164797469)
            ·
              refine ⟨13321495832389223311799051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35523988886371262164797469 13321495832389223311799051)
              ·
                refine ⟨19982243748583834967698577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13321495832389223311799051 19982243748583834967698577)
                ·
                  refine ⟨14986682811437876225773933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19982243748583834967698577 14986682811437876225773933)
                  ·
                    refine ⟨5620006054289203584665225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14986682811437876225773933 5620006054289203584665225)
                    ·
                      refine ⟨4215004540716902688498919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620006054289203584665225 4215004540716902688498919)
                      ·
                        rfl

theorem cell23_8208692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_8208692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208692 prefixEnd_8208692 := by exact prefixLift 8208692
  have htrace : WordTrace (prefixWord ++ tailWord_8208692) baseStart_8208692 baseEnd_8208692 := by
    simpa [prefixWord, tailWord_8208692, baseEnd_8208692] using wordTrace_append hprefix tailTrace_8208692
  have hstable : (prefixWord ++ tailWord_8208692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208692).length < 2 ^ (prefixWord ++ tailWord_8208692).sum := by decide
  have hdescent : baseEnd_8208692 < baseStart_8208692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208702 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_8208702 : Nat := 118140960795 + 8208702 * 2 ^ 59
def prefixEnd_8208702 : Nat := 4983230072969 + 3 ^ 40 * 8208702 * 2
def baseEnd_8208702 : Nat := 1405003225174482549791291

theorem tailTrace_8208702 : CollatzResearch.WordTrace tailWord_8208702 prefixEnd_8208702 1405003225174482549791291 := by
  unfold tailWord_8208702
  simp only [CollatzResearch.WordTrace]
  refine ⟨37424494788410257941623545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199597305538188042355325573 37424494788410257941623545)
  ·
    refine ⟨28068371091307693456217659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37424494788410257941623545 28068371091307693456217659)
    ·
      refine ⟨42102556636961540184326489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28068371091307693456217659 42102556636961540184326489)
      ·
        refine ⟨31576917477721155138244867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42102556636961540184326489 31576917477721155138244867)
        ·
          refine ⟨47365376216581732707367301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31576917477721155138244867 47365376216581732707367301)
          ·
            refine ⟨8881008040609074882631369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47365376216581732707367301 8881008040609074882631369)
            ·
              refine ⟨6660756030456806161973527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8881008040609074882631369 6660756030456806161973527)
              ·
                refine ⟨9991134045685209242960291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6660756030456806161973527 9991134045685209242960291)
                ·
                  refine ⟨14986701068527813864440437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991134045685209242960291 14986701068527813864440437)
                  ·
                    refine ⟨1405003225174482549791291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14986701068527813864440437 1405003225174482549791291)
                    ·
                      rfl

theorem cell23_8208702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_8208702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208702 prefixEnd_8208702 := by exact prefixLift 8208702
  have htrace : WordTrace (prefixWord ++ tailWord_8208702) baseStart_8208702 baseEnd_8208702 := by
    simpa [prefixWord, tailWord_8208702, baseEnd_8208702] using wordTrace_append hprefix tailTrace_8208702
  have hstable : (prefixWord ++ tailWord_8208702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208702).length < 2 ^ (prefixWord ++ tailWord_8208702).sum := by decide
  have hdescent : baseEnd_8208702 < baseStart_8208702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208732 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_8208732 : Nat := 118140960795 + 8208732 * 2 ^ 59
def prefixEnd_8208732 : Nat := 4983230072969 + 3 ^ 40 * 8208732 * 2
def baseEnd_8208732 : Nat := 1405008359981027510666245

theorem tailTrace_8208732 : CollatzResearch.WordTrace tailWord_8208732 prefixEnd_8208732 1405008359981027510666245 := by
  unfold tailWord_8208732
  simp only [CollatzResearch.WordTrace]
  refine ⟨149698526248586689328290225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199598034998115585771053633 149698526248586689328290225)
  ·
    refine ⟨112273894686440016996217669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149698526248586689328290225 112273894686440016996217669)
    ·
      refine ⟨21051355253707503186790813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112273894686440016996217669 21051355253707503186790813)
      ·
        refine ⟨7894258220140313695046555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21051355253707503186790813 7894258220140313695046555)
        ·
          refine ⟨11841387330210470542569833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7894258220140313695046555 11841387330210470542569833)
          ·
            refine ⟨8881040497657852906927375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11841387330210470542569833 8881040497657852906927375)
            ·
              refine ⟨13321560746486779360391063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881040497657852906927375 13321560746486779360391063)
              ·
                refine ⟨19982341119730169040586595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13321560746486779360391063 19982341119730169040586595)
                ·
                  refine ⟨29973511679595253560879893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19982341119730169040586595 29973511679595253560879893)
                  ·
                    refine ⟨1405008359981027510666245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29973511679595253560879893 1405008359981027510666245)
                    ·
                      rfl

theorem cell23_8208732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_8208732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208732 prefixEnd_8208732 := by exact prefixLift 8208732
  have htrace : WordTrace (prefixWord ++ tailWord_8208732) baseStart_8208732 baseEnd_8208732 := by
    simpa [prefixWord, tailWord_8208732, baseEnd_8208732] using wordTrace_append hprefix tailTrace_8208732
  have hstable : (prefixWord ++ tailWord_8208732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208732).length < 2 ^ (prefixWord ++ tailWord_8208732).sum := by decide
  have hdescent : baseEnd_8208732 < baseStart_8208732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208761 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_8208761 : Nat := 118140960795 + 8208761 * 2 ^ 59
def prefixEnd_8208761 : Nat := 4983230072969 + 3 ^ 40 * 8208761 * 2
def baseEnd_8208761 : Nat := 4215039970882062918536101

theorem tailTrace_8208761 : CollatzResearch.WordTrace tailWord_8208761 prefixEnd_8208761 4215039970882062918536101 := by
  unfold tailWord_8208761
  simp only [CollatzResearch.WordTrace]
  refine ⟨299398110214068316609386137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199598740142712211072924091 299398110214068316609386137)
  ·
    refine ⟨224548582660551237457039603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299398110214068316609386137 224548582660551237457039603)
    ·
      refine ⟨336822873990826856185559405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224548582660551237457039603 336822873990826856185559405)
      ·
        refine ⟨126308577746560071069584777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336822873990826856185559405 126308577746560071069584777)
        ·
          refine ⟨94731433309920053302188583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126308577746560071069584777 94731433309920053302188583)
          ·
            refine ⟨142097149964880079953282875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94731433309920053302188583 142097149964880079953282875)
            ·
              refine ⟨213145724947320119929924313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142097149964880079953282875 213145724947320119929924313)
              ·
                refine ⟨159859293710490089947443235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213145724947320119929924313 159859293710490089947443235)
                ·
                  refine ⟨239788940565735134921164853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159859293710490089947443235 239788940565735134921164853)
                  ·
                    refine ⟨22480213178037668898859205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 239788940565735134921164853 22480213178037668898859205)
                    ·
                      refine ⟨4215039970882062918536101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22480213178037668898859205 4215039970882062918536101)
                      ·
                        rfl

theorem cell23_8208761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_8208761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208761 prefixEnd_8208761 := by exact prefixLift 8208761
  have htrace : WordTrace (prefixWord ++ tailWord_8208761) baseStart_8208761 baseEnd_8208761 := by
    simpa [prefixWord, tailWord_8208761, baseEnd_8208761] using wordTrace_append hprefix tailTrace_8208761
  have hstable : (prefixWord ++ tailWord_8208761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208761).length < 2 ^ (prefixWord ++ tailWord_8208761).sum := by decide
  have hdescent : baseEnd_8208761 < baseStart_8208761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208829 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_8208829 : Nat := 118140960795 + 8208829 * 2 ^ 59
def prefixEnd_8208829 : Nat := 4983230072969 + 3 ^ 40 * 8208829 * 2
def baseEnd_8208829 : Nat := 4215074887566568652485789

theorem tailTrace_8208829 : CollatzResearch.WordTrace tailWord_8208829 prefixEnd_8208829 4215074887566568652485789 := by
  unfold tailWord_8208829
  simp only [CollatzResearch.WordTrace]
  refine ⟨299400590377821964222861541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199600393585214642815241027 299400590377821964222861541)
  ·
    refine ⟨56137610695841618291786539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299400590377821964222861541 56137610695841618291786539)
    ·
      refine ⟨84206416043762427437679809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56137610695841618291786539 84206416043762427437679809)
      ·
        refine ⟨63154812032821820578259857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84206416043762427437679809 63154812032821820578259857)
        ·
          refine ⟨47366109024616365433694893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63154812032821820578259857 47366109024616365433694893)
          ·
            refine ⟨17762290884231137037635585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47366109024616365433694893 17762290884231137037635585)
            ·
              refine ⟨13321718163173352778226689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17762290884231137037635585 13321718163173352778226689)
              ·
                refine ⟨9991288622380014583670017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13321718163173352778226689 9991288622380014583670017)
                ·
                  refine ⟨7493466466785010937752513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9991288622380014583670017 7493466466785010937752513)
                  ·
                    refine ⟨5620099850088758203314385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7493466466785010937752513 5620099850088758203314385)
                    ·
                      refine ⟨4215074887566568652485789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620099850088758203314385 4215074887566568652485789)
                      ·
                        rfl

theorem cell23_8208829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_8208829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208829 prefixEnd_8208829 := by exact prefixLift 8208829
  have htrace : WordTrace (prefixWord ++ tailWord_8208829) baseStart_8208829 baseEnd_8208829 := by
    simpa [prefixWord, tailWord_8208829, baseEnd_8208829] using wordTrace_append hprefix tailTrace_8208829
  have hstable : (prefixWord ++ tailWord_8208829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208829).length < 2 ^ (prefixWord ++ tailWord_8208829).sum := by decide
  have hdescent : baseEnd_8208829 < baseStart_8208829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208831 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 5, 7]
def baseStart_8208831 : Nat := 118140960795 + 8208831 * 2 ^ 59
def prefixEnd_8208831 : Nat := 4983230072969 + 3 ^ 40 * 8208831 * 2
def baseEnd_8208831 : Nat := 1405025304842625881553593

theorem tailTrace_8208831 : CollatzResearch.WordTrace tailWord_8208831 prefixEnd_8208831 1405025304842625881553593 := by
  unfold tailWord_8208831
  simp only [CollatzResearch.WordTrace]
  refine ⟨299400663323814718564434347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199600442215876479042956231 299400663323814718564434347)
  ·
    refine ⟨449100994985722077846651521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299400663323814718564434347 449100994985722077846651521)
    ·
      refine ⟨336825746239291558384988641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449100994985722077846651521 336825746239291558384988641)
      ·
        refine ⟨252619309679468668788741481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336825746239291558384988641 252619309679468668788741481)
        ·
          refine ⟨189464482259601501591556111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252619309679468668788741481 189464482259601501591556111)
          ·
            refine ⟨284196723389402252387334167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189464482259601501591556111 284196723389402252387334167)
            ·
              refine ⟨426295085084103378581001251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284196723389402252387334167 426295085084103378581001251)
              ·
                refine ⟨639442627626155067871501877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426295085084103378581001251 639442627626155067871501877)
                ·
                  refine ⟨59947746339952037612953301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 639442627626155067871501877 59947746339952037612953301)
                  ·
                    refine ⟨1405025304842625881553593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59947746339952037612953301 1405025304842625881553593)
                    ·
                      rfl

theorem cell23_8208831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_8208831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208831 prefixEnd_8208831 := by exact prefixLift 8208831
  have htrace : WordTrace (prefixWord ++ tailWord_8208831) baseStart_8208831 baseEnd_8208831 := by
    simpa [prefixWord, tailWord_8208831, baseEnd_8208831] using wordTrace_append hprefix tailTrace_8208831
  have hstable : (prefixWord ++ tailWord_8208831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208831).length < 2 ^ (prefixWord ++ tailWord_8208831).sum := by decide
  have hdescent : baseEnd_8208831 < baseStart_8208831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208895 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 3, 4]
def baseStart_8208895 : Nat := 118140960795 + 8208895 * 2 ^ 59
def prefixEnd_8208895 : Nat := 4983230072969 + 3 ^ 40 * 8208895 * 2
def baseEnd_8208895 : Nat := 1405036259096588464753495

theorem tailTrace_8208895 : CollatzResearch.WordTrace tailWord_8208895 prefixEnd_8208895 1405036259096588464753495 := by
  unfold tailWord_8208895
  simp only [CollatzResearch.WordTrace]
  refine ⟨299402997595582857494764139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199601998397055238329842759 299402997595582857494764139)
  ·
    refine ⟨449104496393374286242146209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299402997595582857494764139 449104496393374286242146209)
    ·
      refine ⟨336828372295030714681609657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449104496393374286242146209 336828372295030714681609657)
      ·
        refine ⟨252621279221273036011207243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336828372295030714681609657 252621279221273036011207243)
        ·
          refine ⟨378931918831909554016810865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252621279221273036011207243 378931918831909554016810865)
          ·
            refine ⟨284198939123932165512608149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378931918831909554016810865 284198939123932165512608149)
            ·
              refine ⟨13321825271434320258403507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284198939123932165512608149 13321825271434320258403507)
              ·
                refine ⟨19982737907151480387605261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13321825271434320258403507 19982737907151480387605261)
                ·
                  refine ⟨7493526715181805145351973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19982737907151480387605261 7493526715181805145351973)
                  ·
                    refine ⟨1405036259096588464753495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7493526715181805145351973 1405036259096588464753495)
                    ·
                      rfl

theorem cell23_8208895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 4].length) (baseStart_8208895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208895 prefixEnd_8208895 := by exact prefixLift 8208895
  have htrace : WordTrace (prefixWord ++ tailWord_8208895) baseStart_8208895 baseEnd_8208895 := by
    simpa [prefixWord, tailWord_8208895, baseEnd_8208895] using wordTrace_append hprefix tailTrace_8208895
  have hstable : (prefixWord ++ tailWord_8208895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208895).length < 2 ^ (prefixWord ++ tailWord_8208895).sum := by decide
  have hdescent : baseEnd_8208895 < baseStart_8208895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208968 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 5, 6]
def baseStart_8208968 : Nat := 118140960795 + 8208968 * 2 ^ 59
def prefixEnd_8208968 : Nat := 4983230072969 + 3 ^ 40 * 8208968 * 2
def baseEnd_8208968 : Nat := 1405048753792514536215883

theorem tailTrace_8208968 : CollatzResearch.WordTrace tailWord_8208968 prefixEnd_8208968 1405048753792514536215883 := by
  unfold tailWord_8208968
  simp only [CollatzResearch.WordTrace]
  refine ⟨149702830062159195481085779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199603773416212260641447705 149702830062159195481085779)
  ·
    refine ⟨224554245093238793221628669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149702830062159195481085779 224554245093238793221628669)
    ·
      refine ⟨84207841909964547458110751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224554245093238793221628669 84207841909964547458110751)
      ·
        refine ⟨126311762864946821187166127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84207841909964547458110751 126311762864946821187166127)
        ·
          refine ⟨189467644297420231780749191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126311762864946821187166127 189467644297420231780749191)
          ·
            refine ⟨284201466446130347671123787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189467644297420231780749191 284201466446130347671123787)
            ·
              refine ⟨426302199669195521506685681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284201466446130347671123787 426302199669195521506685681)
              ·
                refine ⟨319726649751896641130014261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426302199669195521506685681 319726649751896641130014261)
                ·
                  refine ⟨29974373414240310105938837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319726649751896641130014261 29974373414240310105938837)
                  ·
                    refine ⟨1405048753792514536215883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29974373414240310105938837 1405048753792514536215883)
                    ·
                      rfl

theorem cell23_8208968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_8208968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208968 prefixEnd_8208968 := by exact prefixLift 8208968
  have htrace : WordTrace (prefixWord ++ tailWord_8208968) baseStart_8208968 baseEnd_8208968 := by
    simpa [prefixWord, tailWord_8208968, baseEnd_8208968] using wordTrace_append hprefix tailTrace_8208968
  have hstable : (prefixWord ++ tailWord_8208968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208968).length < 2 ^ (prefixWord ++ tailWord_8208968).sum := by decide
  have hdescent : baseEnd_8208968 < baseStart_8208968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8208975 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 2, 6, 2]
def baseStart_8208975 : Nat := 118140960795 + 8208975 * 2 ^ 59
def prefixEnd_8208975 : Nat := 4983230072969 + 3 ^ 40 * 8208975 * 2
def baseEnd_8208975 : Nat := 4215149855742125081260117

theorem tailTrace_8208975 : CollatzResearch.WordTrace tailWord_8208975 prefixEnd_8208975 4215149855742125081260117 := by
  unfold tailWord_8208975
  simp only [CollatzResearch.WordTrace]
  refine ⟨299405915435293031157676379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199603943623528687438450919 299405915435293031157676379)
  ·
    refine ⟨449108873152939546736514569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299405915435293031157676379 449108873152939546736514569)
    ·
      refine ⟨336831654864704660052385927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449108873152939546736514569 336831654864704660052385927)
      ·
        refine ⟨505247482297056990078578891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336831654864704660052385927 505247482297056990078578891)
        ·
          refine ⟨757871223445585485117868337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505247482297056990078578891 757871223445585485117868337)
          ·
            refine ⟨568403417584189113838401253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757871223445585485117868337 568403417584189113838401253)
            ·
              refine ⟨106575640797035458844700235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 568403417584189113838401253 106575640797035458844700235)
              ·
                refine ⟨159863461195553188267050353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106575640797035458844700235 159863461195553188267050353)
                ·
                  refine ⟨119897595896664891200287765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159863461195553188267050353 119897595896664891200287765)
                  ·
                    refine ⟨5620199807656166775013489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119897595896664891200287765 5620199807656166775013489)
                    ·
                      refine ⟨4215149855742125081260117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620199807656166775013489 4215149855742125081260117)
                      ·
                        rfl

theorem cell23_8208975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 6, 2].length) (baseStart_8208975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8208975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8208975 prefixEnd_8208975 := by exact prefixLift 8208975
  have htrace : WordTrace (prefixWord ++ tailWord_8208975) baseStart_8208975 baseEnd_8208975 := by
    simpa [prefixWord, tailWord_8208975, baseEnd_8208975] using wordTrace_append hprefix tailTrace_8208975
  have hstable : (prefixWord ++ tailWord_8208975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8208975).length < 2 ^ (prefixWord ++ tailWord_8208975).sum := by decide
  have hdescent : baseEnd_8208975 < baseStart_8208975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8208975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209075 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 2, 6]
def baseStart_8209075 : Nat := 118140960795 + 8209075 * 2 ^ 59
def prefixEnd_8209075 : Nat := 4983230072969 + 3 ^ 40 * 8209075 * 2
def baseEnd_8209075 : Nat := 1405067067935858230003219

theorem tailTrace_8209075 : CollatzResearch.WordTrace tailWord_8209075 prefixEnd_8209075 1405067067935858230003219 := by
  unfold tailWord_8209075
  simp only [CollatzResearch.WordTrace]
  refine ⟨299409562734930748236316679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199606375156620498824211119 299409562734930748236316679)
  ·
    refine ⟨449114344102396122354475019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299409562734930748236316679 449114344102396122354475019)
    ·
      refine ⟨673671516153594183531712529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449114344102396122354475019 673671516153594183531712529)
      ·
        refine ⟨505253637115195637648784397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673671516153594183531712529 505253637115195637648784397)
        ·
          refine ⟨189470113918198364118294149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505253637115195637648784397 189470113918198364118294149)
          ·
            refine ⟨35525646359662193272180153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189470113918198364118294149 35525646359662193272180153)
            ·
              refine ⟨26644234769746644954135115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35525646359662193272180153 26644234769746644954135115)
              ·
                refine ⟨39966352154619967431202673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26644234769746644954135115 39966352154619967431202673)
                ·
                  refine ⟨29974764115964975573402005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39966352154619967431202673 29974764115964975573402005)
                  ·
                    refine ⟨1405067067935858230003219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29974764115964975573402005 1405067067935858230003219)
                    ·
                      rfl

theorem cell23_8209075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 6].length) (baseStart_8209075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209075 prefixEnd_8209075 := by exact prefixLift 8209075
  have htrace : WordTrace (prefixWord ++ tailWord_8209075) baseStart_8209075 baseEnd_8209075 := by
    simpa [prefixWord, tailWord_8209075, baseEnd_8209075] using wordTrace_append hprefix tailTrace_8209075
  have hstable : (prefixWord ++ tailWord_8209075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209075).length < 2 ^ (prefixWord ++ tailWord_8209075).sum := by decide
  have hdescent : baseEnd_8209075 < baseStart_8209075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209086 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_8209086 : Nat := 118140960795 + 8209086 * 2 ^ 59
def prefixEnd_8209086 : Nat := 4983230072969 + 3 ^ 40 * 8209086 * 2
def baseEnd_8209086 : Nat := 4215206852094774146972107

theorem tailTrace_8209086 : CollatzResearch.WordTrace tailWord_8209086 prefixEnd_8209086 4215206852094774146972107 := by
  unfold tailWord_8209086
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426245492236362139370889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199606642625260598076644741 37426245492236362139370889)
  ·
    refine ⟨28069684119177271604528167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37426245492236362139370889 28069684119177271604528167)
    ·
      refine ⟨42104526178765907406792251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28069684119177271604528167 42104526178765907406792251)
      ·
        refine ⟨63156789268148861110188377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42104526178765907406792251 63156789268148861110188377)
        ·
          refine ⟨47367591951111645832641283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63156789268148861110188377 47367591951111645832641283)
          ·
            refine ⟨71051387926667468748961925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47367591951111645832641283 71051387926667468748961925)
            ·
              refine ⟨13322135236250150390430361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71051387926667468748961925 13322135236250150390430361)
              ·
                refine ⟨9991601427187612792822771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13322135236250150390430361 9991601427187612792822771)
                ·
                  refine ⟨14987402140781419189234157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991601427187612792822771 14987402140781419189234157)
                  ·
                    refine ⟨5620275802793032195962809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14987402140781419189234157 5620275802793032195962809)
                    ·
                      refine ⟨4215206852094774146972107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620275802793032195962809 4215206852094774146972107)
                      ·
                        rfl

theorem cell23_8209086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_8209086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209086 prefixEnd_8209086 := by exact prefixLift 8209086
  have htrace : WordTrace (prefixWord ++ tailWord_8209086) baseStart_8209086 baseEnd_8209086 := by
    simpa [prefixWord, tailWord_8209086, baseEnd_8209086] using wordTrace_append hprefix tailTrace_8209086
  have hstable : (prefixWord ++ tailWord_8209086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209086).length < 2 ^ (prefixWord ++ tailWord_8209086).sum := by decide
  have hdescent : baseEnd_8209086 < baseStart_8209086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209094 : List Nat := [6, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_8209094 : Nat := 118140960795 + 8209094 * 2 ^ 59
def prefixEnd_8209094 : Nat := 4983230072969 + 3 ^ 40 * 8209094 * 2
def baseEnd_8209094 : Nat := 4215210959940010115672071

theorem tailTrace_8209094 : CollatzResearch.WordTrace tailWord_8209094 prefixEnd_8209094 4215210959940010115672071 := by
  unfold tailWord_8209094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9356570491308184827539323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199606837147907942987505557 9356570491308184827539323)
  ·
    refine ⟨14034855736962277241308985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9356570491308184827539323 14034855736962277241308985)
    ·
      refine ⟨10526141802721707930981739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14034855736962277241308985 10526141802721707930981739)
      ·
        refine ⟨15789212704082561896472609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10526141802721707930981739 15789212704082561896472609)
        ·
          refine ⟨11841909528061921422354457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15789212704082561896472609 11841909528061921422354457)
          ·
            refine ⟨8881432146046441066765843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11841909528061921422354457 8881432146046441066765843)
            ·
              refine ⟨13322148219069661600148765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881432146046441066765843 13322148219069661600148765)
              ·
                refine ⟨4995805582151123100055787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13322148219069661600148765 4995805582151123100055787)
                ·
                  refine ⟨7493708373226684650083681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995805582151123100055787 7493708373226684650083681)
                  ·
                    refine ⟨5620281279920013487562761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7493708373226684650083681 5620281279920013487562761)
                    ·
                      refine ⟨4215210959940010115672071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620281279920013487562761 4215210959940010115672071)
                      ·
                        rfl

theorem cell23_8209094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_8209094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209094 prefixEnd_8209094 := by exact prefixLift 8209094
  have htrace : WordTrace (prefixWord ++ tailWord_8209094) baseStart_8209094 baseEnd_8209094 := by
    simpa [prefixWord, tailWord_8209094, baseEnd_8209094] using wordTrace_append hprefix tailTrace_8209094
  have hstable : (prefixWord ++ tailWord_8209094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209094).length < 2 ^ (prefixWord ++ tailWord_8209094).sum := by decide
  have hdescent : baseEnd_8209094 < baseStart_8209094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209095 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_8209095 : Nat := 118140960795 + 8209095 * 2 ^ 59
def prefixEnd_8209095 : Nat := 4983230072969 + 3 ^ 40 * 8209095 * 2
def baseEnd_8209095 : Nat := 4215211473420664611759565

theorem tailTrace_8209095 : CollatzResearch.WordTrace tailWord_8209095 prefixEnd_8209095 4215211473420664611759565 := by
  unfold tailWord_8209095
  simp only [CollatzResearch.WordTrace]
  refine ⟨299410292194858291652044739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199606861463238861101363159 299410292194858291652044739)
  ·
    refine ⟨449115438292287437478067109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299410292194858291652044739 449115438292287437478067109)
    ·
      refine ⟨84209144679803894527137583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449115438292287437478067109 84209144679803894527137583)
      ·
        refine ⟨126313717019705841790706375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84209144679803894527137583 126313717019705841790706375)
        ·
          refine ⟨189470575529558762686059563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126313717019705841790706375 189470575529558762686059563)
          ·
            refine ⟨284205863294338144029089345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189470575529558762686059563 284205863294338144029089345)
            ·
              refine ⟨213154397470753608021817009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284205863294338144029089345 213154397470753608021817009)
              ·
                refine ⟨159865798103065206016362757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213154397470753608021817009 159865798103065206016362757)
                ·
                  refine ⟨29974837144324726128068017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159865798103065206016362757 29974837144324726128068017)
                  ·
                    refine ⟨22481127858243544596051013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29974837144324726128068017 22481127858243544596051013)
                    ·
                      refine ⟨4215211473420664611759565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22481127858243544596051013 4215211473420664611759565)
                      ·
                        rfl

theorem cell23_8209095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_8209095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209095 prefixEnd_8209095 := by exact prefixLift 8209095
  have htrace : WordTrace (prefixWord ++ tailWord_8209095) baseStart_8209095 baseEnd_8209095 := by
    simpa [prefixWord, tailWord_8209095, baseEnd_8209095] using wordTrace_append hprefix tailTrace_8209095
  have hstable : (prefixWord ++ tailWord_8209095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209095).length < 2 ^ (prefixWord ++ tailWord_8209095).sum := by decide
  have hdescent : baseEnd_8209095 < baseStart_8209095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209102 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_8209102 : Nat := 118140960795 + 8209102 * 2 ^ 59
def prefixEnd_8209102 : Nat := 4983230072969 + 3 ^ 40 * 8209102 * 2
def baseEnd_8209102 : Nat := 4215215067785246084372033

theorem tailTrace_8209102 : CollatzResearch.WordTrace tailWord_8209102 prefixEnd_8209102 4215215067785246084372033 := by
  unfold tailWord_8209102
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426318438229116480943695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199607031670555287898366373 37426318438229116480943695)
  ·
    refine ⟨56139477657343674721415543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37426318438229116480943695 56139477657343674721415543)
    ·
      refine ⟨84209216486015512082123315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56139477657343674721415543 84209216486015512082123315)
      ·
        refine ⟨126313824729023268123184973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84209216486015512082123315 126313824729023268123184973)
        ·
          refine ⟨47367684273383725546194365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126313824729023268123184973 47367684273383725546194365)
          ·
            refine ⟨17762881602518897079822887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47367684273383725546194365 17762881602518897079822887)
            ·
              refine ⟨26644322403778345619734331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17762881602518897079822887 26644322403778345619734331)
              ·
                refine ⟨39966483605667518429601497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26644322403778345619734331 39966483605667518429601497)
                ·
                  refine ⟨29974862704250638822201123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39966483605667518429601497 29974862704250638822201123)
                  ·
                    refine ⟨44962294056375958233301685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29974862704250638822201123 44962294056375958233301685)
                    ·
                      refine ⟨4215215067785246084372033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44962294056375958233301685 4215215067785246084372033)
                      ·
                        rfl

theorem cell23_8209102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_8209102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209102 prefixEnd_8209102 := by exact prefixLift 8209102
  have htrace : WordTrace (prefixWord ++ tailWord_8209102) baseStart_8209102 baseEnd_8209102 := by
    simpa [prefixWord, tailWord_8209102, baseEnd_8209102] using wordTrace_append hprefix tailTrace_8209102
  have hstable : (prefixWord ++ tailWord_8209102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209102).length < 2 ^ (prefixWord ++ tailWord_8209102).sum := by decide
  have hdescent : baseEnd_8209102 < baseStart_8209102 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209115 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 3]
def baseStart_8209115 : Nat := 118140960795 + 8209115 * 2 ^ 59
def prefixEnd_8209115 : Nat := 4983230072969 + 3 ^ 40 * 8209115 * 2
def baseEnd_8209115 : Nat := 4215221743033754533509473

theorem tailTrace_8209115 : CollatzResearch.WordTrace tailWord_8209115 prefixEnd_8209115 4215221743033754533509473 := by
  unfold tailWord_8209115
  simp only [CollatzResearch.WordTrace]
  refine ⟨299411021654785835067772799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199607347769857223378515199 299411021654785835067772799)
  ·
    refine ⟨449116532482178752601659199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299411021654785835067772799 449116532482178752601659199)
    ·
      refine ⟨673674798723268128902488799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449116532482178752601659199 673674798723268128902488799)
      ·
        refine ⟨1010512198084902193353733199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673674798723268128902488799 1010512198084902193353733199)
        ·
          refine ⟨1515768297127353290030599799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010512198084902193353733199 1515768297127353290030599799)
          ·
            refine ⟨2273652445691029935045899699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515768297127353290030599799 2273652445691029935045899699)
            ·
              refine ⟨3410478668536544902568849549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273652445691029935045899699 3410478668536544902568849549)
              ·
                refine ⟨1278929500701204338463318581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3410478668536544902568849549 1278929500701204338463318581)
                ·
                  refine ⟨119899640690737906730936117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1278929500701204338463318581 119899640690737906730936117)
                  ·
                    refine ⟨11240591314756678756025261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119899640690737906730936117 11240591314756678756025261)
                    ·
                      refine ⟨4215221743033754533509473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11240591314756678756025261 4215221743033754533509473)
                      ·
                        rfl

theorem cell23_8209115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 3].length) (baseStart_8209115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209115 prefixEnd_8209115 := by exact prefixLift 8209115
  have htrace : WordTrace (prefixWord ++ tailWord_8209115) baseStart_8209115 baseEnd_8209115 := by
    simpa [prefixWord, tailWord_8209115, baseEnd_8209115] using wordTrace_append hprefix tailTrace_8209115
  have hstable : (prefixWord ++ tailWord_8209115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209115).length < 2 ^ (prefixWord ++ tailWord_8209115).sum := by decide
  have hdescent : baseEnd_8209115 < baseStart_8209115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209189 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 2, 4, 2]
def baseStart_8209189 : Nat := 118140960795 + 8209189 * 2 ^ 59
def prefixEnd_8209189 : Nat := 4983230072969 + 3 ^ 40 * 8209189 * 2
def baseEnd_8209189 : Nat := 4215259740602187243984133

theorem tailTrace_8209189 : CollatzResearch.WordTrace tailWord_8209189 prefixEnd_8209189 4215259740602187243984133 := by
  unfold tailWord_8209189
  simp only [CollatzResearch.WordTrace]
  refine ⟨299413720656517745705966621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199609147104345163803977747 299413720656517745705966621)
  ·
    refine ⟨112280145246194154639737483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299413720656517745705966621 112280145246194154639737483)
    ·
      refine ⟨168420217869291231959606225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112280145246194154639737483 168420217869291231959606225)
      ·
        refine ⟨126315163401968423969704669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168420217869291231959606225 126315163401968423969704669)
        ·
          refine ⟨47368186275738158988639251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126315163401968423969704669 47368186275738158988639251)
          ·
            refine ⟨71052279413607238482958877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47368186275738158988639251 71052279413607238482958877)
            ·
              refine ⟨26644604780102714431109579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71052279413607238482958877 26644604780102714431109579)
              ·
                refine ⟨39966907170154071646664369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26644604780102714431109579 39966907170154071646664369)
                ·
                  refine ⟨29975180377615553734998277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39966907170154071646664369 29975180377615553734998277)
                  ·
                    refine ⟨5620346320802916325312177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29975180377615553734998277 5620346320802916325312177)
                    ·
                      refine ⟨4215259740602187243984133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620346320802916325312177 4215259740602187243984133)
                      ·
                        rfl

theorem cell23_8209189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_8209189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209189 prefixEnd_8209189 := by exact prefixLift 8209189
  have htrace : WordTrace (prefixWord ++ tailWord_8209189) baseStart_8209189 baseEnd_8209189 := by
    simpa [prefixWord, tailWord_8209189, baseEnd_8209189] using wordTrace_append hprefix tailTrace_8209189
  have hstable : (prefixWord ++ tailWord_8209189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209189).length < 2 ^ (prefixWord ++ tailWord_8209189).sum := by decide
  have hdescent : baseEnd_8209189 < baseStart_8209189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209206 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_8209206 : Nat := 118140960795 + 8209206 * 2 ^ 59
def prefixEnd_8209206 : Nat := 4983230072969 + 3 ^ 40 * 8209206 * 2
def baseEnd_8209206 : Nat := 4215268469773313677471555

theorem tailTrace_8209206 : CollatzResearch.WordTrace tailWord_8209206 prefixEnd_8209206 4215268469773313677471555 := by
  unfold tailWord_8209206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18713396293591009850583467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199609560464970771739556981 18713396293591009850583467)
  ·
    refine ⟨28070094440386514775875201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18713396293591009850583467 28070094440386514775875201)
    ·
      refine ⟨21052570830289886081906401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28070094440386514775875201 21052570830289886081906401)
      ·
        refine ⟨15789428122717414561429801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21052570830289886081906401 15789428122717414561429801)
        ·
          refine ⟨11842071092038060921072351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15789428122717414561429801 11842071092038060921072351)
          ·
            refine ⟨17763106638057091381608527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11842071092038060921072351 17763106638057091381608527)
            ·
              refine ⟨26644659957085637072412791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17763106638057091381608527 26644659957085637072412791)
              ·
                refine ⟨39966989935628455608619187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26644659957085637072412791 39966989935628455608619187)
                ·
                  refine ⟨59950484903442683412928781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39966989935628455608619187 59950484903442683412928781)
                  ·
                    refine ⟨22481431838791006279848293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59950484903442683412928781 22481431838791006279848293)
                    ·
                      refine ⟨4215268469773313677471555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22481431838791006279848293 4215268469773313677471555)
                      ·
                        rfl

theorem cell23_8209206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_8209206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209206 prefixEnd_8209206 := by exact prefixLift 8209206
  have htrace : WordTrace (prefixWord ++ tailWord_8209206) baseStart_8209206 baseEnd_8209206 := by
    simpa [prefixWord, tailWord_8209206, baseEnd_8209206] using wordTrace_append hprefix tailTrace_8209206
  have hstable : (prefixWord ++ tailWord_8209206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209206).length < 2 ^ (prefixWord ++ tailWord_8209206).sum := by decide
  have hdescent : baseEnd_8209206 < baseStart_8209206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209249 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_8209249 : Nat := 118140960795 + 8209249 * 2 ^ 59
def prefixEnd_8209249 : Nat := 4983230072969 + 3 ^ 40 * 8209249 * 2
def baseEnd_8209249 : Nat := 4215290549441457009233857

theorem tailTrace_8209249 : CollatzResearch.WordTrace tailWord_8209249 prefixEnd_8209249 4215290549441457009233857 := by
  unfold tailWord_8209249
  simp only [CollatzResearch.WordTrace]
  refine ⟨299415909036300375953150801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199610606024200250635433867 299415909036300375953150801)
  ·
    refine ⟨224561931777225281964863101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299415909036300375953150801 224561931777225281964863101)
    ·
      refine ⟨84210724416459480736823663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224561931777225281964863101 84210724416459480736823663)
      ·
        refine ⟨126316086624689221105235495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84210724416459480736823663 126316086624689221105235495)
        ·
          refine ⟨189474129937033831657853243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126316086624689221105235495 189474129937033831657853243)
          ·
            refine ⟨284211194905550747486779865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189474129937033831657853243 284211194905550747486779865)
            ·
              refine ⟨213158396179163060615084899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284211194905550747486779865 213158396179163060615084899)
              ·
                refine ⟨319737594268744590922627349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213158396179163060615084899 319737594268744590922627349)
                ·
                  refine ⟨14987699731347402699498157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319737594268744590922627349 14987699731347402699498157)
                  ·
                    refine ⟨5620387399255276012311809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14987699731347402699498157 5620387399255276012311809)
                    ·
                      refine ⟨4215290549441457009233857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620387399255276012311809 4215290549441457009233857)
                      ·
                        rfl

theorem cell23_8209249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_8209249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209249 prefixEnd_8209249 := by exact prefixLift 8209249
  have htrace : WordTrace (prefixWord ++ tailWord_8209249) baseStart_8209249 baseEnd_8209249 := by
    simpa [prefixWord, tailWord_8209249, baseEnd_8209249] using wordTrace_append hprefix tailTrace_8209249
  have hstable : (prefixWord ++ tailWord_8209249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209249).length < 2 ^ (prefixWord ++ tailWord_8209249).sum := by decide
  have hdescent : baseEnd_8209249 < baseStart_8209249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209256 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_8209256 : Nat := 118140960795 + 8209256 * 2 ^ 59
def prefixEnd_8209256 : Nat := 4983230072969 + 3 ^ 40 * 8209256 * 2
def baseEnd_8209256 : Nat := 4215294143806038481846325

theorem tailTrace_8209256 : CollatzResearch.WordTrace tailWord_8209256 prefixEnd_8209256 4215294143806038481846325 := by
  unfold tailWord_8209256
  simp only [CollatzResearch.WordTrace]
  refine ⟨149708082173637508074327811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199610776231516677432437081 149708082173637508074327811)
  ·
    refine ⟨224562123260456262111491717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149708082173637508074327811 224562123260456262111491717)
    ·
      refine ⟨42105398111335549145904697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224562123260456262111491717 42105398111335549145904697)
      ·
        refine ⟨31579048583501661859428523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42105398111335549145904697 31579048583501661859428523)
        ·
          refine ⟨47368572875252492789142785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31579048583501661859428523 47368572875252492789142785)
          ·
            refine ⟨35526429656439369591857089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47368572875252492789142785 35526429656439369591857089)
            ·
              refine ⟨26644822242329527193892817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35526429656439369591857089 26644822242329527193892817)
              ·
                refine ⟨19983616681747145395419613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26644822242329527193892817 19983616681747145395419613)
                ·
                  refine ⟨7493856255655179523282355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19983616681747145395419613 7493856255655179523282355)
                  ·
                    refine ⟨11240784383482769284923533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7493856255655179523282355 11240784383482769284923533)
                    ·
                      refine ⟨4215294143806038481846325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11240784383482769284923533 4215294143806038481846325)
                      ·
                        rfl

theorem cell23_8209256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_8209256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209256 prefixEnd_8209256 := by exact prefixLift 8209256
  have htrace : WordTrace (prefixWord ++ tailWord_8209256) baseStart_8209256 baseEnd_8209256 := by
    simpa [prefixWord, tailWord_8209256, baseEnd_8209256] using wordTrace_append hprefix tailTrace_8209256
  have hstable : (prefixWord ++ tailWord_8209256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209256).length < 2 ^ (prefixWord ++ tailWord_8209256).sum := by decide
  have hdescent : baseEnd_8209256 < baseStart_8209256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209273 : List Nat := [1, 2, 1, 3, 2, 3, 3, 3, 1, 1, 3]
def baseStart_8209273 : Nat := 118140960795 + 8209273 * 2 ^ 59
def prefixEnd_8209273 : Nat := 4983230072969 + 3 ^ 40 * 8209273 * 2
def baseEnd_8209273 : Nat := 4215302872977164915333747

theorem tailTrace_8209273 : CollatzResearch.WordTrace tailWord_8209273 prefixEnd_8209273 4215302872977164915333747 := by
  unfold tailWord_8209273
  simp only [CollatzResearch.WordTrace]
  refine ⟨299416784388213428052024473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199611189592142285368016315 299416784388213428052024473)
  ·
    refine ⟨224562588291160071039018355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299416784388213428052024473 224562588291160071039018355)
    ·
      refine ⟨336843882436740106558527533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224562588291160071039018355 336843882436740106558527533)
      ·
        refine ⟨126316455913777539959447825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336843882436740106558527533 126316455913777539959447825)
        ·
          refine ⟨94737341935333154969585869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126316455913777539959447825 94737341935333154969585869)
          ·
            refine ⟨35526503225749933113594701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94737341935333154969585869 35526503225749933113594701)
            ·
              refine ⟨13322438709656224917598013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35526503225749933113594701 13322438709656224917598013)
              ·
                refine ⟨4995914516121084344099255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13322438709656224917598013 4995914516121084344099255)
                ·
                  refine ⟨7493871774181626516148883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995914516121084344099255 7493871774181626516148883)
                  ·
                    refine ⟨11240807661272439774223325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7493871774181626516148883 11240807661272439774223325)
                    ·
                      refine ⟨4215302872977164915333747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11240807661272439774223325 4215302872977164915333747)
                      ·
                        rfl

theorem cell23_8209273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_8209273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209273 prefixEnd_8209273 := by exact prefixLift 8209273
  have htrace : WordTrace (prefixWord ++ tailWord_8209273) baseStart_8209273 baseEnd_8209273 := by
    simpa [prefixWord, tailWord_8209273, baseEnd_8209273] using wordTrace_append hprefix tailTrace_8209273
  have hstable : (prefixWord ++ tailWord_8209273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209273).length < 2 ^ (prefixWord ++ tailWord_8209273).sum := by decide
  have hdescent : baseEnd_8209273 < baseStart_8209273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209279 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 4]
def baseStart_8209279 : Nat := 118140960795 + 8209279 * 2 ^ 59
def prefixEnd_8209279 : Nat := 4983230072969 + 3 ^ 40 * 8209279 * 2
def baseEnd_8209279 : Nat := 4215305953861091891858719

theorem tailTrace_8209279 : CollatzResearch.WordTrace tailWord_8209279 prefixEnd_8209279 4215305953861091891858719 := by
  unfold tailWord_8209279
  simp only [CollatzResearch.WordTrace]
  refine ⟨299417003226191691076742891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199611335484127794051161927 299417003226191691076742891)
  ·
    refine ⟨449125504839287536615114337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299417003226191691076742891 449125504839287536615114337)
    ·
      refine ⟨336844128629465652461335753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449125504839287536615114337 336844128629465652461335753)
      ·
        refine ⟨252633096472099239346001815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336844128629465652461335753 252633096472099239346001815)
        ·
          refine ⟨378949644708148859019002723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252633096472099239346001815 378949644708148859019002723)
          ·
            refine ⟨568424467062223288528504085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378949644708148859019002723 568424467062223288528504085)
            ·
              refine ⟨26644896893541716649773629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 568424467062223288528504085 26644896893541716649773629)
              ·
                refine ⟨9991836335078143743665111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26644896893541716649773629 9991836335078143743665111)
                ·
                  refine ⟨14987754502617215615497667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991836335078143743665111 14987754502617215615497667)
                  ·
                    refine ⟨22481631753925823423246501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14987754502617215615497667 22481631753925823423246501)
                    ·
                      refine ⟨4215305953861091891858719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22481631753925823423246501 4215305953861091891858719)
                      ·
                        rfl

theorem cell23_8209279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_8209279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209279 prefixEnd_8209279 := by exact prefixLift 8209279
  have htrace : WordTrace (prefixWord ++ tailWord_8209279) baseStart_8209279 baseEnd_8209279 := by
    simpa [prefixWord, tailWord_8209279, baseEnd_8209279] using wordTrace_append hprefix tailTrace_8209279
  have hstable : (prefixWord ++ tailWord_8209279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209279).length < 2 ^ (prefixWord ++ tailWord_8209279).sum := by decide
  have hdescent : baseEnd_8209279 < baseStart_8209279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209289 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 4, 4]
def baseStart_8209289 : Nat := 118140960795 + 8209289 * 2 ^ 59
def prefixEnd_8209289 : Nat := 4983230072969 + 3 ^ 40 * 8209289 * 2
def baseEnd_8209289 : Nat := 1405103696222545617577891

theorem tailTrace_8209289 : CollatzResearch.WordTrace tailWord_8209289 prefixEnd_8209289 1405103696222545617577891 := by
  unfold tailWord_8209289
  simp only [CollatzResearch.WordTrace]
  refine ⟨299417367956155462784606921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199611578637436975189737947 299417367956155462784606921)
  ·
    refine ⟨224563025967116597088455191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299417367956155462784606921 224563025967116597088455191)
    ·
      refine ⟨336844538950674895632682787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224563025967116597088455191 336844538950674895632682787)
      ·
        refine ⟨505266808426012343449024181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336844538950674895632682787 505266808426012343449024181)
        ·
          refine ⟨47368763289938657198346017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 505266808426012343449024181 47368763289938657198346017)
          ·
            refine ⟨35526572467453992898759513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47368763289938657198346017 35526572467453992898759513)
            ·
              refine ⟨26644929350590494674069635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35526572467453992898759513 26644929350590494674069635)
              ·
                refine ⟨39967394025885742011104453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26644929350590494674069635 39967394025885742011104453)
                ·
                  refine ⟨7493886379853576627082085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39967394025885742011104453 7493886379853576627082085)
                  ·
                    refine ⟨1405103696222545617577891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7493886379853576627082085 1405103696222545617577891)
                    ·
                      rfl

theorem cell23_8209289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 4].length) (baseStart_8209289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209289 prefixEnd_8209289 := by exact prefixLift 8209289
  have htrace : WordTrace (prefixWord ++ tailWord_8209289) baseStart_8209289 baseEnd_8209289 := by
    simpa [prefixWord, tailWord_8209289, baseEnd_8209289] using wordTrace_append hprefix tailTrace_8209289
  have hstable : (prefixWord ++ tailWord_8209289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209289).length < 2 ^ (prefixWord ++ tailWord_8209289).sum := by decide
  have hdescent : baseEnd_8209289 < baseStart_8209289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209292 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_8209292 : Nat := 118140960795 + 8209292 * 2 ^ 59
def prefixEnd_8209292 : Nat := 4983230072969 + 3 ^ 40 * 8209292 * 2
def baseEnd_8209292 : Nat := 4215312629109600340996159

theorem tailTrace_8209292 : CollatzResearch.WordTrace tailWord_8209292 prefixEnd_8209292 4215312629109600340996159 := by
  unfold tailWord_8209292
  simp only [CollatzResearch.WordTrace]
  refine ⟨149708738687572297148483065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199611651583429729531310753 149708738687572297148483065)
  ·
    refine ⟨112281554015679222861362299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149708738687572297148483065 112281554015679222861362299)
    ·
      refine ⟨168422331023518834292043449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112281554015679222861362299 168422331023518834292043449)
      ·
        refine ⟨126316748267639125719032587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168422331023518834292043449 126316748267639125719032587)
        ·
          refine ⟨189475122401458688578548881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126316748267639125719032587 189475122401458688578548881)
          ·
            refine ⟨142106341801094016433911661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189475122401458688578548881 142106341801094016433911661)
            ·
              refine ⟨53289878175410256162716873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142106341801094016433911661 53289878175410256162716873)
              ·
                refine ⟨39967408631557692122037655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53289878175410256162716873 39967408631557692122037655)
                ·
                  refine ⟨59951112947336538183056483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39967408631557692122037655 59951112947336538183056483)
                  ·
                    refine ⟨89926669421004807274584725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59951112947336538183056483 89926669421004807274584725)
                    ·
                      refine ⟨4215312629109600340996159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89926669421004807274584725 4215312629109600340996159)
                      ·
                        rfl

theorem cell23_8209292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_8209292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209292 prefixEnd_8209292 := by exact prefixLift 8209292
  have htrace : WordTrace (prefixWord ++ tailWord_8209292) baseStart_8209292 baseEnd_8209292 := by
    simpa [prefixWord, tailWord_8209292, baseEnd_8209292] using wordTrace_append hprefix tailTrace_8209292
  have hstable : (prefixWord ++ tailWord_8209292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209292).length < 2 ^ (prefixWord ++ tailWord_8209292).sum := by decide
  have hdescent : baseEnd_8209292 < baseStart_8209292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209309 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_8209309 : Nat := 118140960795 + 8209309 * 2 ^ 59
def prefixEnd_8209309 : Nat := 4983230072969 + 3 ^ 40 * 8209309 * 2
def baseEnd_8209309 : Nat := 4215321358280726774483581

theorem tailTrace_8209309 : CollatzResearch.WordTrace tailWord_8209309 prefixEnd_8209309 4215321358280726774483581 := by
  unfold tailWord_8209309
  simp only [CollatzResearch.WordTrace]
  refine ⟨299418097416083006200334981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199612064944055337466889987 299418097416083006200334981)
  ·
    refine ⟨56140893265515563662562809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299418097416083006200334981 56140893265515563662562809)
    ·
      refine ⟨42105669949136672746922107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56140893265515563662562809 42105669949136672746922107)
      ·
        refine ⟨63158504923705009120383161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42105669949136672746922107 63158504923705009120383161)
        ·
          refine ⟨47368878692778756840287371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63158504923705009120383161 47368878692778756840287371)
          ·
            refine ⟨71053318039168135260431057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47368878692778756840287371 71053318039168135260431057)
            ·
              refine ⟨53289988529376101445323293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71053318039168135260431057 53289988529376101445323293)
              ·
                refine ⟨19983745698516038041996235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53289988529376101445323293 19983745698516038041996235)
                ·
                  refine ⟨29975618547774057062994353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19983745698516038041996235 29975618547774057062994353)
                  ·
                    refine ⟨22481713910830542797245765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29975618547774057062994353 22481713910830542797245765)
                    ·
                      refine ⟨4215321358280726774483581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22481713910830542797245765 4215321358280726774483581)
                      ·
                        rfl

theorem cell23_8209309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_8209309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209309 prefixEnd_8209309 := by exact prefixLift 8209309
  have htrace : WordTrace (prefixWord ++ tailWord_8209309) baseStart_8209309 baseEnd_8209309 := by
    simpa [prefixWord, tailWord_8209309, baseEnd_8209309] using wordTrace_append hprefix tailTrace_8209309
  have hstable : (prefixWord ++ tailWord_8209309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209309).length < 2 ^ (prefixWord ++ tailWord_8209309).sum := by decide
  have hdescent : baseEnd_8209309 < baseStart_8209309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209313 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_8209313 : Nat := 118140960795 + 8209313 * 2 ^ 59
def prefixEnd_8209313 : Nat := 4983230072969 + 3 ^ 40 * 8209313 * 2
def baseEnd_8209313 : Nat := 4215323412203344758833563

theorem tailTrace_8209313 : CollatzResearch.WordTrace tailWord_8209313 prefixEnd_8209313 4215323412203344758833563 := by
  unfold tailWord_8209313
  simp only [CollatzResearch.WordTrace]
  refine ⟨299418243308068514883480593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199612162205379009922320395 299418243308068514883480593)
  ·
    refine ⟨224563682481051386162610445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299418243308068514883480593 224563682481051386162610445)
    ·
      refine ⟨84211380930394269810978917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224563682481051386162610445 84211380930394269810978917)
      ·
        refine ⟨15789633924448925589558547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84211380930394269810978917 15789633924448925589558547)
        ·
          refine ⟨23684450886673388384337821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15789633924448925589558547 23684450886673388384337821)
          ·
            refine ⟨8881669082502520644126683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23684450886673388384337821 8881669082502520644126683)
            ·
              refine ⟨13322503623753780966190025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881669082502520644126683 13322503623753780966190025)
              ·
                refine ⟨9991877717815335724642519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13322503623753780966190025 9991877717815335724642519)
                ·
                  refine ⟨14987816576723003586963779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991877717815335724642519 14987816576723003586963779)
                  ·
                    refine ⟨22481724865084505380445669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14987816576723003586963779 22481724865084505380445669)
                    ·
                      refine ⟨4215323412203344758833563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22481724865084505380445669 4215323412203344758833563)
                      ·
                        rfl

theorem cell23_8209313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_8209313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209313 prefixEnd_8209313 := by exact prefixLift 8209313
  have htrace : WordTrace (prefixWord ++ tailWord_8209313) baseStart_8209313 baseEnd_8209313 := by
    simpa [prefixWord, tailWord_8209313, baseEnd_8209313] using wordTrace_append hprefix tailTrace_8209313
  have hstable : (prefixWord ++ tailWord_8209313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209313).length < 2 ^ (prefixWord ++ tailWord_8209313).sum := by decide
  have hdescent : baseEnd_8209313 < baseStart_8209313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209333 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_8209333 : Nat := 118140960795 + 8209333 * 2 ^ 59
def prefixEnd_8209333 : Nat := 4983230072969 + 3 ^ 40 * 8209333 * 2
def baseEnd_8209333 : Nat := 4215333681816434680583471

theorem tailTrace_8209333 : CollatzResearch.WordTrace tailWord_8209333 prefixEnd_8209333 4215333681816434680583471 := by
  unfold tailWord_8209333
  simp only [CollatzResearch.WordTrace]
  refine ⟨299418972767996058299208653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199612648511997372199472435 299418972767996058299208653)
  ·
    refine ⟨112282114787998521862203245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299418972767996058299208653 112282114787998521862203245)
    ·
      refine ⟨42105793045499445698326217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112282114787998521862203245 42105793045499445698326217)
      ·
        refine ⟨31579344784124584273744663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42105793045499445698326217 31579344784124584273744663)
        ·
          refine ⟨47369017176186876410616995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31579344784124584273744663 47369017176186876410616995)
          ·
            refine ⟨71053525764280314615925493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47369017176186876410616995 71053525764280314615925493)
            ·
              refine ⟨6661268040401279495243015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71053525764280314615925493 6661268040401279495243015)
              ·
                refine ⟨9991902060601919242864523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661268040401279495243015 9991902060601919242864523)
                ·
                  refine ⟨14987853090902878864296785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991902060601919242864523 14987853090902878864296785)
                  ·
                    refine ⟨11240889818177159148222589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14987853090902878864296785 11240889818177159148222589)
                    ·
                      refine ⟨4215333681816434680583471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11240889818177159148222589 4215333681816434680583471)
                      ·
                        rfl

theorem cell23_8209333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_8209333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209333 prefixEnd_8209333 := by exact prefixLift 8209333
  have htrace : WordTrace (prefixWord ++ tailWord_8209333) baseStart_8209333 baseEnd_8209333 := by
    simpa [prefixWord, tailWord_8209333, baseEnd_8209333] using wordTrace_append hprefix tailTrace_8209333
  have hstable : (prefixWord ++ tailWord_8209333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209333).length < 2 ^ (prefixWord ++ tailWord_8209333).sum := by decide
  have hdescent : baseEnd_8209333 < baseStart_8209333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209356 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 5, 3, 2]
def baseStart_8209356 : Nat := 118140960795 + 8209356 * 2 ^ 59
def prefixEnd_8209356 : Nat := 4983230072969 + 3 ^ 40 * 8209356 * 2
def baseEnd_8209356 : Nat := 4215345491871488090595865

theorem tailTrace_8209356 : CollatzResearch.WordTrace tailWord_8209356 prefixEnd_8209356 4215345491871488090595865 := by
  unfold tailWord_8209356
  simp only [CollatzResearch.WordTrace]
  refine ⟨149709905823456366613647961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199613207764608488818197281 149709905823456366613647961)
  ·
    refine ⟨112282429367592274960235971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149709905823456366613647961 112282429367592274960235971)
    ·
      refine ⟨168423644051388412440353957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112282429367592274960235971 168423644051388412440353957)
      ·
        refine ⟨31579433259635327332566367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168423644051388412440353957 31579433259635327332566367)
        ·
          refine ⟨47369149889452990998849551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31579433259635327332566367 47369149889452990998849551)
          ·
            refine ⟨71053724834179486498274327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47369149889452990998849551 71053724834179486498274327)
            ·
              refine ⟨106580587251269229747411491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71053724834179486498274327 106580587251269229747411491)
              ·
                refine ⟨159870880876903844621117237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106580587251269229747411491 159870880876903844621117237)
                ·
                  refine ⟨14987895082209735433229741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159870880876903844621117237 14987895082209735433229741)
                  ·
                    refine ⟨5620460655828650787461153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14987895082209735433229741 5620460655828650787461153)
                    ·
                      refine ⟨4215345491871488090595865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620460655828650787461153 4215345491871488090595865)
                      ·
                        rfl

theorem cell23_8209356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_8209356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209356 prefixEnd_8209356 := by exact prefixLift 8209356
  have htrace : WordTrace (prefixWord ++ tailWord_8209356) baseStart_8209356 baseEnd_8209356 := by
    simpa [prefixWord, tailWord_8209356, baseEnd_8209356] using wordTrace_append hprefix tailTrace_8209356
  have hstable : (prefixWord ++ tailWord_8209356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209356).length < 2 ^ (prefixWord ++ tailWord_8209356).sum := by decide
  have hdescent : baseEnd_8209356 < baseStart_8209356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209373 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_8209373 : Nat := 118140960795 + 8209373 * 2 ^ 59
def prefixEnd_8209373 : Nat := 4983230072969 + 3 ^ 40 * 8209373 * 2
def baseEnd_8209373 : Nat := 4215354221042614524083287

theorem tailTrace_8209373 : CollatzResearch.WordTrace tailWord_8209373 prefixEnd_8209373 4215354221042614524083287 := by
  unfold tailWord_8209373
  simp only [CollatzResearch.WordTrace]
  refine ⟨299420431687851145130664773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199613621125234096753776515 299420431687851145130664773)
  ·
    refine ⟨56141330941472089711999645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299420431687851145130664773 56141330941472089711999645)
    ·
      refine ⟨21052999103052033641999867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56141330941472089711999645 21052999103052033641999867)
      ·
        refine ⟨31579498654578050462999801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21052999103052033641999867 31579498654578050462999801)
        ·
          refine ⟨23684623990933537847249851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31579498654578050462999801 23684623990933537847249851)
          ·
            refine ⟨35526935986400306770874777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23684623990933537847249851 35526935986400306770874777)
            ·
              refine ⟨26645201989800230078156083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35526935986400306770874777 26645201989800230078156083)
              ·
                refine ⟨39967802984700345117234125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26645201989800230078156083 39967802984700345117234125)
                ·
                  refine ⟨14987926119262629418962797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39967802984700345117234125 14987926119262629418962797)
                  ·
                    refine ⟨5620472294723486032111049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14987926119262629418962797 5620472294723486032111049)
                    ·
                      refine ⟨4215354221042614524083287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620472294723486032111049 4215354221042614524083287)
                      ·
                        rfl

theorem cell23_8209373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_8209373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209373 prefixEnd_8209373 := by exact prefixLift 8209373
  have htrace : WordTrace (prefixWord ++ tailWord_8209373) baseStart_8209373 baseEnd_8209373 := by
    simpa [prefixWord, tailWord_8209373, baseEnd_8209373] using wordTrace_append hprefix tailTrace_8209373
  have hstable : (prefixWord ++ tailWord_8209373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209373).length < 2 ^ (prefixWord ++ tailWord_8209373).sum := by decide
  have hdescent : baseEnd_8209373 < baseStart_8209373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209390 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_8209390 : Nat := 118140960795 + 8209390 * 2 ^ 59
def prefixEnd_8209390 : Nat := 4983230072969 + 3 ^ 40 * 8209390 * 2
def baseEnd_8209390 : Nat := 4215362950213740957570709

theorem tailTrace_8209390 : CollatzResearch.WordTrace tailWord_8209390 prefixEnd_8209390 4215362950213740957570709 := by
  unfold tailWord_8209390
  simp only [CollatzResearch.WordTrace]
  refine ⟨37427631466098694629254203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199614034485859704689355749 37427631466098694629254203)
  ·
    refine ⟨56141447199148041943881305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37427631466098694629254203 56141447199148041943881305)
    ·
      refine ⟨42106085399361031457910979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56141447199148041943881305 42106085399361031457910979)
      ·
        refine ⟨63159128099041547186866469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42106085399361031457910979 63159128099041547186866469)
        ·
          refine ⟨11842336518570290097537463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63159128099041547186866469 11842336518570290097537463)
          ·
            refine ⟨17763504777855435146306195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11842336518570290097537463 17763504777855435146306195)
            ·
              refine ⟨26645257166783152719459293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17763504777855435146306195 26645257166783152719459293)
              ·
                refine ⟨9991971437543682269797235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26645257166783152719459293 9991971437543682269797235)
                ·
                  refine ⟨14987957156315523404695853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991971437543682269797235 14987957156315523404695853)
                  ·
                    refine ⟨5620483933618321276760945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14987957156315523404695853 5620483933618321276760945)
                    ·
                      refine ⟨4215362950213740957570709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620483933618321276760945 4215362950213740957570709)
                      ·
                        rfl

theorem cell23_8209390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_8209390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209390 prefixEnd_8209390 := by exact prefixLift 8209390
  have htrace : WordTrace (prefixWord ++ tailWord_8209390) baseStart_8209390 baseEnd_8209390 := by
    simpa [prefixWord, tailWord_8209390, baseEnd_8209390] using wordTrace_append hprefix tailTrace_8209390
  have hstable : (prefixWord ++ tailWord_8209390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209390).length < 2 ^ (prefixWord ++ tailWord_8209390).sum := by decide
  have hdescent : baseEnd_8209390 < baseStart_8209390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209392 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 11]
def baseStart_8209392 : Nat := 118140960795 + 8209392 * 2 ^ 59
def prefixEnd_8209392 : Nat := 4983230072969 + 3 ^ 40 * 8209392 * 2
def baseEnd_8209392 : Nat := 468373775241672216638411

theorem tailTrace_8209392 : CollatzResearch.WordTrace tailWord_8209392 prefixEnd_8209392 468373775241672216638411 := by
  unfold tailWord_8209392
  simp only [CollatzResearch.WordTrace]
  refine ⟨149710562337391155687803215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199614083116521540917070953 149710562337391155687803215)
  ·
    refine ⟨224565843506086733531704823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149710562337391155687803215 224565843506086733531704823)
    ·
      refine ⟨336848765259130100297557235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224565843506086733531704823 336848765259130100297557235)
      ·
        refine ⟨505273147888695150446335853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336848765259130100297557235 505273147888695150446335853)
        ·
          refine ⟨189477430458260681417375945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505273147888695150446335853 189477430458260681417375945)
          ·
            refine ⟨142108072843695511063031959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189477430458260681417375945 142108072843695511063031959)
            ·
              refine ⟨213162109265543266594547939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142108072843695511063031959 213162109265543266594547939)
              ·
                refine ⟨319743163898314899891821909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213162109265543266594547939 319743163898314899891821909)
                ·
                  refine ⟨468373775241672216638411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 319743163898314899891821909 468373775241672216638411)
                  ·
                    rfl

theorem cell23_8209392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 11].length) (baseStart_8209392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209392 prefixEnd_8209392 := by exact prefixLift 8209392
  have htrace : WordTrace (prefixWord ++ tailWord_8209392) baseStart_8209392 baseEnd_8209392 := by
    simpa [prefixWord, tailWord_8209392, baseEnd_8209392] using wordTrace_append hprefix tailTrace_8209392
  have hstable : (prefixWord ++ tailWord_8209392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209392).length < 2 ^ (prefixWord ++ tailWord_8209392).sum := by decide
  have hdescent : baseEnd_8209392 < baseStart_8209392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209409 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 7]
def baseStart_8209409 : Nat := 118140960795 + 8209409 * 2 ^ 59
def prefixEnd_8209409 : Nat := 4983230072969 + 3 ^ 40 * 8209409 * 2
def baseEnd_8209409 : Nat := 468374745149575153692569

theorem tailTrace_8209409 : CollatzResearch.WordTrace tailWord_8209409 prefixEnd_8209409 468374745149575153692569 := by
  unfold tailWord_8209409
  simp only [CollatzResearch.WordTrace]
  refine ⟨299421744715720723278975281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199614496477147148852650187 299421744715720723278975281)
  ·
    refine ⟨224566308536790542459231461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299421744715720723278975281 224566308536790542459231461)
    ·
      refine ⟨42106182850648226711105899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224566308536790542459231461 42106182850648226711105899)
      ·
        refine ⟨63159274275972340066658849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42106182850648226711105899 63159274275972340066658849)
        ·
          refine ⟨47369455706979255049994137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63159274275972340066658849 47369455706979255049994137)
          ·
            refine ⟨35527091780234441287495603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47369455706979255049994137 35527091780234441287495603)
            ·
              refine ⟨53290637670351661931243405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35527091780234441287495603 53290637670351661931243405)
              ·
                refine ⟨19983989126381873224216277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53290637670351661931243405 19983989126381873224216277)
                ·
                  refine ⟨468374745149575153692569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19983989126381873224216277 468374745149575153692569)
                  ·
                    rfl

theorem cell23_8209409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 7].length) (baseStart_8209409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209409 prefixEnd_8209409 := by exact prefixLift 8209409
  have htrace : WordTrace (prefixWord ++ tailWord_8209409) baseStart_8209409 baseEnd_8209409 := by
    simpa [prefixWord, tailWord_8209409, baseEnd_8209409] using wordTrace_append hprefix tailTrace_8209409
  have hstable : (prefixWord ++ tailWord_8209409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209409).length < 2 ^ (prefixWord ++ tailWord_8209409).sum := by decide
  have hdescent : baseEnd_8209409 < baseStart_8209409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209439 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 1, 7]
def baseStart_8209439 : Nat := 118140960795 + 8209439 * 2 ^ 59
def prefixEnd_8209439 : Nat := 4983230072969 + 3 ^ 40 * 8209439 * 2
def baseEnd_8209439 : Nat := 1405129370255270421952661

theorem tailTrace_8209439 : CollatzResearch.WordTrace tailWord_8209439 prefixEnd_8209439 1405129370255270421952661 := by
  unfold tailWord_8209439
  simp only [CollatzResearch.WordTrace]
  refine ⟨299422838905612038402567371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199615225937074692268378247 299422838905612038402567371)
  ·
    refine ⟨449134258358418057603851057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299422838905612038402567371 449134258358418057603851057)
    ·
      refine ⟨336850693768813543202888293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449134258358418057603851057 336850693768813543202888293)
      ·
        refine ⟨63159505081652539350541555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336850693768813543202888293 63159505081652539350541555)
        ·
          refine ⟨94739257622478809025812333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63159505081652539350541555 94739257622478809025812333)
          ·
            refine ⟨35527221608429553384679625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94739257622478809025812333 35527221608429553384679625)
            ·
              refine ⟨26645416206322165038509719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35527221608429553384679625 26645416206322165038509719)
              ·
                refine ⟨39968124309483247557764579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26645416206322165038509719 39968124309483247557764579)
                ·
                  refine ⟨59952186464224871336646869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39968124309483247557764579 59952186464224871336646869)
                  ·
                    refine ⟨1405129370255270421952661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59952186464224871336646869 1405129370255270421952661)
                    ·
                      rfl

theorem cell23_8209439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_8209439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209439 prefixEnd_8209439 := by exact prefixLift 8209439
  have htrace : WordTrace (prefixWord ++ tailWord_8209439) baseStart_8209439 baseEnd_8209439 := by
    simpa [prefixWord, tailWord_8209439, baseEnd_8209439] using wordTrace_append hprefix tailTrace_8209439
  have hstable : (prefixWord ++ tailWord_8209439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209439).length < 2 ^ (prefixWord ++ tailWord_8209439).sum := by decide
  have hdescent : baseEnd_8209439 < baseStart_8209439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
