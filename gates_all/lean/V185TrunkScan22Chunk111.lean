import V185TrunkScan22Chunk110

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_994798 : List Nat := [4, 1, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_994798 : Nat := 118140960795 + 994798 * 2 ^ 59
def prefixEnd_994798 : Nat := 4983230072969 + 3 ^ 40 * 994798 * 2
def baseEnd_994798 : Nat := 340539685421002721300009

theorem tailTrace_994798 : CollatzResearch.WordTrace tailWord_994798 prefixEnd_994798 340539685421002721300009 := by
  unfold tailWord_994798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4535407981253027352155131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24188842566682812544827365 4535407981253027352155131)
  ·
    refine ⟨6803111971879541028232697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4535407981253027352155131 6803111971879541028232697)
    ·
      refine ⟨5102333978909655771174523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6803111971879541028232697 5102333978909655771174523)
      ·
        refine ⟨7653500968364483656761785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5102333978909655771174523 7653500968364483656761785)
        ·
          refine ⟨5740125726273362742571339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7653500968364483656761785 5740125726273362742571339)
          ·
            refine ⟨8610188589410044113857009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740125726273362742571339 8610188589410044113857009)
            ·
              refine ⟨6457641442057533085392757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8610188589410044113857009 6457641442057533085392757)
              ·
                refine ⟨605403885192893726755571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6457641442057533085392757 605403885192893726755571)
                ·
                  refine ⟨908105827789340590133357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605403885192893726755571 908105827789340590133357)
                  ·
                    refine ⟨340539685421002721300009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 908105827789340590133357 340539685421002721300009)
                    ·
                      rfl

theorem cell22_994798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_994798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994798 prefixEnd_994798 := by exact prefixLift 994798
  have htrace : WordTrace (prefixWord ++ tailWord_994798) baseStart_994798 baseEnd_994798 := by
    simpa [prefixWord, tailWord_994798, baseEnd_994798] using wordTrace_append hprefix tailTrace_994798
  have hstable : (prefixWord ++ tailWord_994798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994798).length < 2 ^ (prefixWord ++ tailWord_994798).sum := by decide
  have hdescent : baseEnd_994798 < baseStart_994798 := by decide
  rcases family_descends (prefixWord ++ tailWord_994798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994824 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_994824 : Nat := 118140960795 + 994824 * 2 ^ 59
def prefixEnd_994824 : Nat := 4983230072969 + 3 ^ 40 * 994824 * 2
def baseEnd_994824 : Nat := 340548585752347320149929

theorem tailTrace_994824 : CollatzResearch.WordTrace tailWord_994824 prefixEnd_994824 340548585752347320149929 := by
  unfold tailWord_994824
  simp only [CollatzResearch.WordTrace]
  refine ⟨18142106073965012628843763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24189474765286683505125017 18142106073965012628843763)
  ·
    refine ⟨27213159110947518943265645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18142106073965012628843763 27213159110947518943265645)
    ·
      refine ⟨10204934666605319603724617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27213159110947518943265645 10204934666605319603724617)
      ·
        refine ⟨7653700999953989702793463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10204934666605319603724617 7653700999953989702793463)
        ·
          refine ⟨11480551499930984554190195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7653700999953989702793463 11480551499930984554190195)
          ·
            refine ⟨17220827249896476831285293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11480551499930984554190195 17220827249896476831285293)
            ·
              refine ⟨6457810218711178811731985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17220827249896476831285293 6457810218711178811731985)
              ·
                refine ⟨4843357664033384108798989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6457810218711178811731985 4843357664033384108798989)
                ·
                  refine ⟨1816259124012519040799621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4843357664033384108798989 1816259124012519040799621)
                  ·
                    refine ⟨340548585752347320149929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1816259124012519040799621 340548585752347320149929)
                    ·
                      rfl

theorem cell22_994824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_994824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994824 prefixEnd_994824 := by exact prefixLift 994824
  have htrace : WordTrace (prefixWord ++ tailWord_994824) baseStart_994824 baseEnd_994824 := by
    simpa [prefixWord, tailWord_994824, baseEnd_994824] using wordTrace_append hprefix tailTrace_994824
  have hstable : (prefixWord ++ tailWord_994824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994824).length < 2 ^ (prefixWord ++ tailWord_994824).sum := by decide
  have hdescent : baseEnd_994824 < baseStart_994824 := by decide
  rcases family_descends (prefixWord ++ tailWord_994824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994871 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 4, 3]
def baseStart_994871 : Nat := 118140960795 + 994871 * 2 ^ 59
def prefixEnd_994871 : Nat := 4983230072969 + 3 ^ 40 * 994871 * 2
def baseEnd_994871 : Nat := 340564674812854864224785

theorem tailTrace_994871 : CollatzResearch.WordTrace tailWord_994871 prefixEnd_994871 340564674812854864224785 := by
  unfold tailWord_994871
  simp only [CollatzResearch.WordTrace]
  refine ⟨36285926378759752284648467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24190617585839834856432311 36285926378759752284648467)
  ·
    refine ⟨54428889568139628426972701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36285926378759752284648467 54428889568139628426972701)
    ·
      refine ⟨20410833588052360660114763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54428889568139628426972701 20410833588052360660114763)
      ·
        refine ⟨30616250382078540990172145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20410833588052360660114763 30616250382078540990172145)
        ·
          refine ⟨22962187786558905742629109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30616250382078540990172145 22962187786558905742629109)
          ·
            refine ⟨2152705104989897413371479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22962187786558905742629109 2152705104989897413371479)
            ·
              refine ⟨3229057657484846120057219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152705104989897413371479 3229057657484846120057219)
              ·
                refine ⟨4843586486227269180085829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229057657484846120057219 4843586486227269180085829)
                ·
                  refine ⟨908172466167612971266093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4843586486227269180085829 908172466167612971266093)
                  ·
                    refine ⟨340564674812854864224785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 908172466167612971266093 340564674812854864224785)
                    ·
                      rfl

theorem cell22_994871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_994871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994871 prefixEnd_994871 := by exact prefixLift 994871
  have htrace : WordTrace (prefixWord ++ tailWord_994871) baseStart_994871 baseEnd_994871 := by
    simpa [prefixWord, tailWord_994871, baseEnd_994871] using wordTrace_append hprefix tailTrace_994871
  have hstable : (prefixWord ++ tailWord_994871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994871).length < 2 ^ (prefixWord ++ tailWord_994871).sum := by decide
  have hdescent : baseEnd_994871 < baseStart_994871 := by decide
  rcases family_descends (prefixWord ++ tailWord_994871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994944 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_994944 : Nat := 118140960795 + 994944 * 2 ^ 59
def prefixEnd_994944 : Nat := 4983230072969 + 3 ^ 40 * 994944 * 2
def baseEnd_994944 : Nat := 340589664204707007149561

theorem tailTrace_994944 : CollatzResearch.WordTrace tailWord_994944 prefixEnd_994944 340589664204707007149561 := by
  unfold tailWord_994944
  simp only [CollatzResearch.WordTrace]
  refine ⟨18144294453747642876027943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24192392604996857168037257 18144294453747642876027943)
  ·
    refine ⟨27216441680621464314041915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18144294453747642876027943 27216441680621464314041915)
    ·
      refine ⟨40824662520932196471062873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27216441680621464314041915 40824662520932196471062873)
      ·
        refine ⟨30618496890699147353297155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40824662520932196471062873 30618496890699147353297155)
        ·
          refine ⟨45927745336048721029945733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30618496890699147353297155 45927745336048721029945733)
          ·
            refine ⟨8611452250509135193114825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45927745336048721029945733 8611452250509135193114825)
            ·
              refine ⟨6458589187881851394836119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8611452250509135193114825 6458589187881851394836119)
              ·
                refine ⟨9687883781822777092254179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458589187881851394836119 9687883781822777092254179)
                ·
                  refine ⟨14531825672734165638381269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687883781822777092254179 14531825672734165638381269)
                  ·
                    refine ⟨340589664204707007149561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14531825672734165638381269 340589664204707007149561)
                    ·
                      rfl

theorem cell22_994944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_994944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_994944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_994944 prefixEnd_994944 := by exact prefixLift 994944
  have htrace : WordTrace (prefixWord ++ tailWord_994944) baseStart_994944 baseEnd_994944 := by
    simpa [prefixWord, tailWord_994944, baseEnd_994944] using wordTrace_append hprefix tailTrace_994944
  have hstable : (prefixWord ++ tailWord_994944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994944).length < 2 ^ (prefixWord ++ tailWord_994944).sum := by decide
  have hdescent : baseEnd_994944 < baseStart_994944 := by decide
  rcases family_descends (prefixWord ++ tailWord_994944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995019 : List Nat := [1, 1, 1, 1, 3, 2, 1, 12]
def baseStart_995019 : Nat := 118140960795 + 995019 * 2 ^ 59
def prefixEnd_995019 : Nat := 4983230072969 + 3 ^ 40 * 995019 * 2
def baseEnd_995019 : Nat := 37846148693047979058259

theorem tailTrace_995019 : CollatzResearch.WordTrace tailWord_995019 prefixEnd_995019 37846148693047979058259 := by
  unfold tailWord_995019
  simp only [CollatzResearch.WordTrace]
  refine ⟨36291324382223573561036111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24194216254815715707357407 36291324382223573561036111)
  ·
    refine ⟨54436986573335360341554167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36291324382223573561036111 54436986573335360341554167)
    ·
      refine ⟨81655479860003040512331251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54436986573335360341554167 81655479860003040512331251)
      ·
        refine ⟨122483219790004560768496877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81655479860003040512331251 122483219790004560768496877)
        ·
          refine ⟨45931207421251710288186329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122483219790004560768496877 45931207421251710288186329)
          ·
            refine ⟨34448405565938782716139747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45931207421251710288186329 34448405565938782716139747)
            ·
              refine ⟨51672608348908174074209621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34448405565938782716139747 51672608348908174074209621)
              ·
                refine ⟨37846148693047979058259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 51672608348908174074209621 37846148693047979058259)
                ·
                  rfl

theorem cell22_995019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 12].length) (baseStart_995019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995019 prefixEnd_995019 := by exact prefixLift 995019
  have htrace : WordTrace (prefixWord ++ tailWord_995019) baseStart_995019 baseEnd_995019 := by
    simpa [prefixWord, tailWord_995019, baseEnd_995019] using wordTrace_append hprefix tailTrace_995019
  have hstable : (prefixWord ++ tailWord_995019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995019).length < 2 ^ (prefixWord ++ tailWord_995019).sum := by decide
  have hdescent : baseEnd_995019 < baseStart_995019 := by decide
  rcases family_descends (prefixWord ++ tailWord_995019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995068 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_995068 : Nat := 118140960795 + 995068 * 2 ^ 59
def prefixEnd_995068 : Nat := 4983230072969 + 3 ^ 40 * 995068 * 2
def baseEnd_995068 : Nat := 340632111938812017049181

theorem tailTrace_995068 : CollatzResearch.WordTrace tailWord_995068 prefixEnd_995068 340632111938812017049181 := by
  unfold tailWord_995068
  simp only [CollatzResearch.WordTrace]
  refine ⟨18146555779523027464784929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24195407706030703286379905 18146555779523027464784929)
  ·
    refine ⟨13609916834642270598588697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18146555779523027464784929 13609916834642270598588697)
    ·
      refine ⟨10207437625981702948941523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13609916834642270598588697 10207437625981702948941523)
      ·
        refine ⟨15311156438972554423412285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207437625981702948941523 15311156438972554423412285)
        ·
          refine ⟨5741683664614707908779607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15311156438972554423412285 5741683664614707908779607)
          ·
            refine ⟨8612525496922061863169411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741683664614707908779607 8612525496922061863169411)
            ·
              refine ⟨12918788245383092794754117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612525496922061863169411 12918788245383092794754117)
              ·
                refine ⟨2422272796009329899016397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12918788245383092794754117 2422272796009329899016397)
                ·
                  refine ⟨908352298503498712131149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2422272796009329899016397 908352298503498712131149)
                  ·
                    refine ⟨340632111938812017049181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 908352298503498712131149 340632111938812017049181)
                    ·
                      rfl

theorem cell22_995068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_995068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995068 prefixEnd_995068 := by exact prefixLift 995068
  have htrace : WordTrace (prefixWord ++ tailWord_995068) baseStart_995068 baseEnd_995068 := by
    simpa [prefixWord, tailWord_995068, baseEnd_995068] using wordTrace_append hprefix tailTrace_995068
  have hstable : (prefixWord ++ tailWord_995068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995068).length < 2 ^ (prefixWord ++ tailWord_995068).sum := by decide
  have hdescent : baseEnd_995068 < baseStart_995068 := by decide
  rcases family_descends (prefixWord ++ tailWord_995068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995096 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_995096 : Nat := 118140960795 + 995096 * 2 ^ 59
def prefixEnd_995096 : Nat := 4983230072969 + 3 ^ 40 * 995096 * 2
def baseEnd_995096 : Nat := 340641696911029277349095

theorem tailTrace_995096 : CollatzResearch.WordTrace tailWord_995096 prefixEnd_995096 340641696911029277349095 := by
  unfold tailWord_995096
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147066401472307855794571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24196088535296410474392761 18147066401472307855794571)
  ·
    refine ⟨27220599602208461783691857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18147066401472307855794571 27220599602208461783691857)
    ·
      refine ⟨20415449701656346337768893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27220599602208461783691857 20415449701656346337768893)
      ·
        refine ⟨7655793638121129876663335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20415449701656346337768893 7655793638121129876663335)
        ·
          refine ⟨11483690457181694814995003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655793638121129876663335 11483690457181694814995003)
          ·
            refine ⟨17225535685772542222492505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483690457181694814995003 17225535685772542222492505)
            ·
              refine ⟨12919151764329406666869379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17225535685772542222492505 12919151764329406666869379)
              ·
                refine ⟨19378727646494110000304069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12919151764329406666869379 19378727646494110000304069)
                ·
                  refine ⟨3633511433717645625057013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19378727646494110000304069 3633511433717645625057013)
                  ·
                    refine ⟨340641696911029277349095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3633511433717645625057013 340641696911029277349095)
                    ·
                      rfl

theorem cell22_995096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_995096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995096 prefixEnd_995096 := by exact prefixLift 995096
  have htrace : WordTrace (prefixWord ++ tailWord_995096) baseStart_995096 baseEnd_995096 := by
    simpa [prefixWord, tailWord_995096, baseEnd_995096] using wordTrace_append hprefix tailTrace_995096
  have hstable : (prefixWord ++ tailWord_995096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995096).length < 2 ^ (prefixWord ++ tailWord_995096).sum := by decide
  have hdescent : baseEnd_995096 < baseStart_995096 := by decide
  rcases family_descends (prefixWord ++ tailWord_995096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995128 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_995128 : Nat := 118140960795 + 995128 * 2 ^ 59
def prefixEnd_995128 : Nat := 4983230072969 + 3 ^ 40 * 995128 * 2
def baseEnd_995128 : Nat := 340652651164991860548997

theorem tailTrace_995128 : CollatzResearch.WordTrace tailWord_995128 prefixEnd_995128 340652651164991860548997 := by
  unfold tailWord_995128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147649969414342588377019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24196866625885790117836025 18147649969414342588377019)
  ·
    refine ⟨27221474954121513882565529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18147649969414342588377019 27221474954121513882565529)
    ·
      refine ⟨20416106215591135411924147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27221474954121513882565529 20416106215591135411924147)
      ·
        refine ⟨30624159323386703117886221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20416106215591135411924147 30624159323386703117886221)
        ·
          refine ⟨11484059746270013669207333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30624159323386703117886221 11484059746270013669207333)
          ·
            refine ⟨2153261202425627562976375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11484059746270013669207333 2153261202425627562976375)
            ·
              refine ⟨3229891803638441344464563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153261202425627562976375 3229891803638441344464563)
              ·
                refine ⟨4844837705457662016696845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229891803638441344464563 4844837705457662016696845)
                ·
                  refine ⟨1816814139546623256261317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4844837705457662016696845 1816814139546623256261317)
                  ·
                    refine ⟨340652651164991860548997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1816814139546623256261317 340652651164991860548997)
                    ·
                      rfl

theorem cell22_995128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_995128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995128 prefixEnd_995128 := by exact prefixLift 995128
  have htrace : WordTrace (prefixWord ++ tailWord_995128) baseStart_995128 baseEnd_995128 := by
    simpa [prefixWord, tailWord_995128, baseEnd_995128] using wordTrace_append hprefix tailTrace_995128
  have hstable : (prefixWord ++ tailWord_995128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995128).length < 2 ^ (prefixWord ++ tailWord_995128).sum := by decide
  have hdescent : baseEnd_995128 < baseStart_995128 := by decide
  rcases family_descends (prefixWord ++ tailWord_995128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995145 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 1, 4]
def baseStart_995145 : Nat := 118140960795 + 995145 * 2 ^ 59
def prefixEnd_995145 : Nat := 4983230072969 + 3 ^ 40 * 995145 * 2
def baseEnd_995145 : Nat := 340658470612409482873945

theorem tailTrace_995145 : CollatzResearch.WordTrace tailWord_995145 prefixEnd_995145 340658470612409482873945 := by
  unfold tailWord_995145
  simp only [CollatzResearch.WordTrace]
  refine ⟨36295919979767097080122889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24197279986511398053415259 36295919979767097080122889)
  ·
    refine ⟨27221939984825322810092167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36295919979767097080122889 27221939984825322810092167)
    ·
      refine ⟨40832909977237984215138251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27221939984825322810092167 40832909977237984215138251)
      ·
        refine ⟨61249364965856976322707377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40832909977237984215138251 61249364965856976322707377)
        ·
          refine ⟨45937023724392732242030533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61249364965856976322707377 45937023724392732242030533)
          ·
            refine ⟨8613191948323637295380725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45937023724392732242030533 8613191948323637295380725)
            ·
              refine ⟨807486745155340996441943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8613191948323637295380725 807486745155340996441943)
              ·
                refine ⟨1211230117733011494662915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807486745155340996441943 1211230117733011494662915)
                ·
                  refine ⟨1816845176599517241994373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211230117733011494662915 1816845176599517241994373)
                  ·
                    refine ⟨340658470612409482873945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1816845176599517241994373 340658470612409482873945)
                    ·
                      rfl

theorem cell22_995145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 4].length) (baseStart_995145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995145 prefixEnd_995145 := by exact prefixLift 995145
  have htrace : WordTrace (prefixWord ++ tailWord_995145) baseStart_995145 baseEnd_995145 := by
    simpa [prefixWord, tailWord_995145, baseEnd_995145] using wordTrace_append hprefix tailTrace_995145
  have hstable : (prefixWord ++ tailWord_995145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995145).length < 2 ^ (prefixWord ++ tailWord_995145).sum := by decide
  have hdescent : baseEnd_995145 < baseStart_995145 := by decide
  rcases family_descends (prefixWord ++ tailWord_995145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995175 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 2, 3]
def baseStart_995175 : Nat := 118140960795 + 995175 * 2 ^ 59
def prefixEnd_995175 : Nat := 4983230072969 + 3 ^ 40 * 995175 * 2
def baseEnd_995175 : Nat := 340668740225499404623853

theorem tailTrace_995175 : CollatzResearch.WordTrace tailWord_995175 prefixEnd_995175 340668740225499404623853 := by
  unfold tailWord_995175
  simp only [CollatzResearch.WordTrace]
  refine ⟨36297014169658412203714979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24198009446438941469143319 36297014169658412203714979)
  ·
    refine ⟨54445521254487618305572469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36297014169658412203714979 54445521254487618305572469)
    ·
      refine ⟨5104267617608214216147419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54445521254487618305572469 5104267617608214216147419)
      ·
        refine ⟨7656401426412321324221129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104267617608214216147419 7656401426412321324221129)
        ·
          refine ⟨5742301069809240993165847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7656401426412321324221129 5742301069809240993165847)
          ·
            refine ⟨8613451604713861489748771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742301069809240993165847 8613451604713861489748771)
            ·
              refine ⟨12920177407070792234623157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613451604713861489748771 12920177407070792234623157)
              ·
                refine ⟨1211266631912886771995921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12920177407070792234623157 1211266631912886771995921)
                ·
                  refine ⟨908449973934665078996941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1211266631912886771995921 908449973934665078996941)
                  ·
                    refine ⟨340668740225499404623853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 908449973934665078996941 340668740225499404623853)
                    ·
                      rfl

theorem cell22_995175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_995175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995175 prefixEnd_995175 := by exact prefixLift 995175
  have htrace : WordTrace (prefixWord ++ tailWord_995175) baseStart_995175 baseEnd_995175 := by
    simpa [prefixWord, tailWord_995175, baseEnd_995175] using wordTrace_append hprefix tailTrace_995175
  have hstable : (prefixWord ++ tailWord_995175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995175).length < 2 ^ (prefixWord ++ tailWord_995175).sum := by decide
  have hdescent : baseEnd_995175 < baseStart_995175 := by decide
  rcases family_descends (prefixWord ++ tailWord_995175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995308 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_995308 : Nat := 118140960795 + 995308 * 2 ^ 59
def prefixEnd_995308 : Nat := 4983230072969 + 3 ^ 40 * 995308 * 2
def baseEnd_995308 : Nat := 340714268843531391048445

theorem tailTrace_995308 : CollatzResearch.WordTrace tailWord_995308 prefixEnd_995308 340714268843531391048445 := by
  unfold tailWord_995308
  simp only [CollatzResearch.WordTrace]
  refine ⟨18150932539088287959153289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24201243385451050612204385 18150932539088287959153289)
  ·
    refine ⟨13613199404316215969364967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18150932539088287959153289 13613199404316215969364967)
    ·
      refine ⟨20419799106474323954047451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13613199404316215969364967 20419799106474323954047451)
      ·
        refine ⟨30629698659711485931071177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20419799106474323954047451 30629698659711485931071177)
        ·
          refine ⟨22972273994783614448303383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30629698659711485931071177 22972273994783614448303383)
          ·
            refine ⟨34458410992175421672455075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22972273994783614448303383 34458410992175421672455075)
            ·
              refine ⟨51687616488263132508682613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34458410992175421672455075 51687616488263132508682613)
              ·
                refine ⟨4845714045774668672688995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51687616488263132508682613 4845714045774668672688995)
                ·
                  refine ⟨7268571068662003009033493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845714045774668672688995 7268571068662003009033493)
                  ·
                    refine ⟨340714268843531391048445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7268571068662003009033493 340714268843531391048445)
                    ·
                      rfl

theorem cell22_995308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_995308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995308 prefixEnd_995308 := by exact prefixLift 995308
  have htrace : WordTrace (prefixWord ++ tailWord_995308) baseStart_995308 baseEnd_995308 := by
    simpa [prefixWord, tailWord_995308, baseEnd_995308] using wordTrace_append hprefix tailTrace_995308
  have hstable : (prefixWord ++ tailWord_995308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995308).length < 2 ^ (prefixWord ++ tailWord_995308).sum := by decide
  have hdescent : baseEnd_995308 < baseStart_995308 := by decide
  rcases family_descends (prefixWord ++ tailWord_995308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995310 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_995310 : Nat := 118140960795 + 995310 * 2 ^ 59
def prefixEnd_995310 : Nat := 4983230072969 + 3 ^ 40 * 995310 * 2
def baseEnd_995310 : Nat := 340714953484404052498439

theorem tailTrace_995310 : CollatzResearch.WordTrace tailWord_995310 prefixEnd_995310 340714953484404052498439 := by
  unfold tailWord_995310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4537742253021166282484923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24201292016112886839919589 4537742253021166282484923)
  ·
    refine ⟨6806613379531749423727385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4537742253021166282484923 6806613379531749423727385)
    ·
      refine ⟨5104960034648812067795539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6806613379531749423727385 5104960034648812067795539)
      ·
        refine ⟨7657440051973218101693309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104960034648812067795539 7657440051973218101693309)
        ·
          refine ⟨2871540019489956788134991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7657440051973218101693309 2871540019489956788134991)
          ·
            refine ⟨4307310029234935182202487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871540019489956788134991 4307310029234935182202487)
            ·
              refine ⟨6460965043852402773303731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307310029234935182202487 6460965043852402773303731)
              ·
                refine ⟨9691447565778604159955597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460965043852402773303731 9691447565778604159955597)
                ·
                  refine ⟨3634292837166976559983349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9691447565778604159955597 3634292837166976559983349)
                  ·
                    refine ⟨340714953484404052498439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3634292837166976559983349 340714953484404052498439)
                    ·
                      rfl

theorem cell22_995310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_995310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995310 prefixEnd_995310 := by exact prefixLift 995310
  have htrace : WordTrace (prefixWord ++ tailWord_995310) baseStart_995310 baseEnd_995310 := by
    simpa [prefixWord, tailWord_995310, baseEnd_995310] using wordTrace_append hprefix tailTrace_995310
  have hstable : (prefixWord ++ tailWord_995310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995310).length < 2 ^ (prefixWord ++ tailWord_995310).sum := by decide
  have hdescent : baseEnd_995310 < baseStart_995310 := by decide
  rcases family_descends (prefixWord ++ tailWord_995310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995325 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_995325 : Nat := 118140960795 + 995325 * 2 ^ 59
def prefixEnd_995325 : Nat := 4983230072969 + 3 ^ 40 * 995325 * 2
def baseEnd_995325 : Nat := 340720088290949013373393

theorem tailTrace_995325 : CollatzResearch.WordTrace tailWord_995325 prefixEnd_995325 340720088290949013373393 := by
  unfold tailWord_995325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36302485119114987821675429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24201656746076658547783619 36302485119114987821675429)
  ·
    refine ⟨6806715959834060216564143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36302485119114987821675429 6806715959834060216564143)
    ·
      refine ⟨10210073939751090324846215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6806715959834060216564143 10210073939751090324846215)
      ·
        refine ⟨15315110909626635487269323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210073939751090324846215 15315110909626635487269323)
        ·
          refine ⟨22972666364439953230903985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15315110909626635487269323 22972666364439953230903985)
          ·
            refine ⟨17229499773329964923177989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22972666364439953230903985 17229499773329964923177989)
            ·
              refine ⟨3230531207499368423095873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17229499773329964923177989 3230531207499368423095873)
              ·
                refine ⟨2422898405624526317321905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230531207499368423095873 2422898405624526317321905)
                ·
                  refine ⟨1817173804218394737991429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2422898405624526317321905 1817173804218394737991429)
                  ·
                    refine ⟨340720088290949013373393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1817173804218394737991429 340720088290949013373393)
                    ·
                      rfl

theorem cell22_995325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_995325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995325 prefixEnd_995325 := by exact prefixLift 995325
  have htrace : WordTrace (prefixWord ++ tailWord_995325) baseStart_995325 baseEnd_995325 := by
    simpa [prefixWord, tailWord_995325, baseEnd_995325] using wordTrace_append hprefix tailTrace_995325
  have hstable : (prefixWord ++ tailWord_995325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995325).length < 2 ^ (prefixWord ++ tailWord_995325).sum := by decide
  have hdescent : baseEnd_995325 < baseStart_995325 := by decide
  rcases family_descends (prefixWord ++ tailWord_995325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995353 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_995353 : Nat := 118140960795 + 995353 * 2 ^ 59
def prefixEnd_995353 : Nat := 4983230072969 + 3 ^ 40 * 995353 * 2
def baseEnd_995353 : Nat := 340729673263166273673307

theorem tailTrace_995353 : CollatzResearch.WordTrace tailWord_995353 prefixEnd_995353 340729673263166273673307 := by
  unfold tailWord_995353
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303506363013548603694713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24202337575342365735796475 36303506363013548603694713)
  ·
    refine ⟨27227629772260161452771035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36303506363013548603694713 27227629772260161452771035)
    ·
      refine ⟨40841444658390242179156553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27227629772260161452771035 40841444658390242179156553)
      ·
        refine ⟨30631083493792681634367415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40841444658390242179156553 30631083493792681634367415)
        ·
          refine ⟨45946625240689022451551123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30631083493792681634367415 45946625240689022451551123)
          ·
            refine ⟨68919937861033533677326685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45946625240689022451551123 68919937861033533677326685)
            ·
              refine ⟨25844976697887575128997507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68919937861033533677326685 25844976697887575128997507)
              ·
                refine ⟨38767465046831362693496261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25844976697887575128997507 38767465046831362693496261)
                ·
                  refine ⟨7268899696280880505030549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38767465046831362693496261 7268899696280880505030549)
                  ·
                    refine ⟨340729673263166273673307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7268899696280880505030549 340729673263166273673307)
                    ·
                      rfl

theorem cell22_995353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_995353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995353 prefixEnd_995353 := by exact prefixLift 995353
  have htrace : WordTrace (prefixWord ++ tailWord_995353) baseStart_995353 baseEnd_995353 := by
    simpa [prefixWord, tailWord_995353, baseEnd_995353] using wordTrace_append hprefix tailTrace_995353
  have hstable : (prefixWord ++ tailWord_995353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995353).length < 2 ^ (prefixWord ++ tailWord_995353).sum := by decide
  have hdescent : baseEnd_995353 < baseStart_995353 := by decide
  rcases family_descends (prefixWord ++ tailWord_995353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995357 : List Nat := [1, 4, 2, 2, 2, 2, 3, 6]
def baseStart_995357 : Nat := 118140960795 + 995357 * 2 ^ 59
def prefixEnd_995357 : Nat := 4983230072969 + 3 ^ 40 * 995357 * 2
def baseEnd_995357 : Nat := 37859004727212399619255

theorem tailTrace_995357 : CollatzResearch.WordTrace tailWord_995357 prefixEnd_995357 37859004727212399619255 := by
  unfold tailWord_995357
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303652254999057286840325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24202434836666038191226883 36303652254999057286840325)
  ·
    refine ⟨6806934797812323241282561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36303652254999057286840325 6806934797812323241282561)
    ·
      refine ⟨5105201098359242430961921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6806934797812323241282561 5105201098359242430961921)
      ·
        refine ⟨3828900823769431823221441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5105201098359242430961921 3828900823769431823221441)
        ·
          refine ⟨2871675617827073867416081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3828900823769431823221441 2871675617827073867416081)
          ·
            refine ⟨2153756713370305400562061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2871675617827073867416081 2153756713370305400562061)
            ·
              refine ⟨807658767513864525210773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2153756713370305400562061 807658767513864525210773)
              ·
                refine ⟨37859004727212399619255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 807658767513864525210773 37859004727212399619255)
                ·
                  rfl

theorem cell22_995357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 6].length) (baseStart_995357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995357 prefixEnd_995357 := by exact prefixLift 995357
  have htrace : WordTrace (prefixWord ++ tailWord_995357) baseStart_995357 baseEnd_995357 := by
    simpa [prefixWord, tailWord_995357, baseEnd_995357] using wordTrace_append hprefix tailTrace_995357
  have hstable : (prefixWord ++ tailWord_995357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995357).length < 2 ^ (prefixWord ++ tailWord_995357).sum := by decide
  have hdescent : baseEnd_995357 < baseStart_995357 := by decide
  rcases family_descends (prefixWord ++ tailWord_995357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995389 : List Nat := [1, 4, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_995389 : Nat := 118140960795 + 995389 * 2 ^ 59
def prefixEnd_995389 : Nat := 4983230072969 + 3 ^ 40 * 995389 * 2
def baseEnd_995389 : Nat := 340741996798874179773197

theorem tailTrace_995389 : CollatzResearch.WordTrace tailWord_995389 prefixEnd_995389 340741996798874179773197 := by
  unfold tailWord_995389
  simp only [CollatzResearch.WordTrace]
  refine ⟨36304819390883126752005221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24203212927255417834670147 36304819390883126752005221)
  ·
    refine ⟨6807153635790586266000979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36304819390883126752005221 6807153635790586266000979)
    ·
      refine ⟨10210730453685879399001469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6807153635790586266000979 10210730453685879399001469)
      ·
        refine ⟨3829023920132204774625551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10210730453685879399001469 3829023920132204774625551)
        ·
          refine ⟨5743535880198307161938327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829023920132204774625551 5743535880198307161938327)
          ·
            refine ⟨8615303820297460742907491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743535880198307161938327 8615303820297460742907491)
            ·
              refine ⟨12922955730446191114361237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8615303820297460742907491 12922955730446191114361237)
              ·
                refine ⟨605763549864665208485683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12922955730446191114361237 605763549864665208485683)
                ·
                  refine ⟨908645324796997812728525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605763549864665208485683 908645324796997812728525)
                  ·
                    refine ⟨340741996798874179773197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 908645324796997812728525 340741996798874179773197)
                    ·
                      rfl

theorem cell22_995389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_995389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995389 prefixEnd_995389 := by exact prefixLift 995389
  have htrace : WordTrace (prefixWord ++ tailWord_995389) baseStart_995389 baseEnd_995389 := by
    simpa [prefixWord, tailWord_995389, baseEnd_995389] using wordTrace_append hprefix tailTrace_995389
  have hstable : (prefixWord ++ tailWord_995389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995389).length < 2 ^ (prefixWord ++ tailWord_995389).sum := by decide
  have hdescent : baseEnd_995389 < baseStart_995389 := by decide
  rcases family_descends (prefixWord ++ tailWord_995389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995415 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 3, 4]
def baseStart_995415 : Nat := 118140960795 + 995415 * 2 ^ 59
def prefixEnd_995415 : Nat := 4983230072969 + 3 ^ 40 * 995415 * 2
def baseEnd_995415 : Nat := 340750897130218778623117

theorem tailTrace_995415 : CollatzResearch.WordTrace tailWord_995415 prefixEnd_995415 340750897130218778623117 := by
  unfold tailWord_995415
  simp only [CollatzResearch.WordTrace]
  refine ⟨36305767688788933192451699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24203845125859288794967799 36305767688788933192451699)
  ·
    refine ⟨54458651533183399788677549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36305767688788933192451699 54458651533183399788677549)
    ·
      refine ⟨20421994324943774920754081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54458651533183399788677549 20421994324943774920754081)
      ·
        refine ⟨15316495743707831190565561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20421994324943774920754081 15316495743707831190565561)
        ·
          refine ⟨11487371807780873392924171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15316495743707831190565561 11487371807780873392924171)
          ·
            refine ⟨17231057711671310089386257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487371807780873392924171 17231057711671310089386257)
            ·
              refine ⟨12923293283753482567039693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17231057711671310089386257 12923293283753482567039693)
              ·
                refine ⟨4846234981407555962639885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12923293283753482567039693 4846234981407555962639885)
                ·
                  refine ⟨1817338118027833485989957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4846234981407555962639885 1817338118027833485989957)
                  ·
                    refine ⟨340750897130218778623117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1817338118027833485989957 340750897130218778623117)
                    ·
                      rfl

theorem cell22_995415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_995415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995415 prefixEnd_995415 := by exact prefixLift 995415
  have htrace : WordTrace (prefixWord ++ tailWord_995415) baseStart_995415 baseEnd_995415 := by
    simpa [prefixWord, tailWord_995415, baseEnd_995415] using wordTrace_append hprefix tailTrace_995415
  have hstable : (prefixWord ++ tailWord_995415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995415).length < 2 ^ (prefixWord ++ tailWord_995415).sum := by decide
  have hdescent : baseEnd_995415 < baseStart_995415 := by decide
  rcases family_descends (prefixWord ++ tailWord_995415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995447 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 6]
def baseStart_995447 : Nat := 118140960795 + 995447 * 2 ^ 59
def prefixEnd_995447 : Nat := 4983230072969 + 3 ^ 40 * 995447 * 2
def baseEnd_995447 : Nat := 113587283794727120607673

theorem tailTrace_995447 : CollatzResearch.WordTrace tailWord_995447 prefixEnd_995447 113587283794727120607673 := by
  unfold tailWord_995447
  simp only [CollatzResearch.WordTrace]
  refine ⟨36306934824673002657616595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24204623216448668438411063 36306934824673002657616595)
  ·
    refine ⟨54460402237009503986424893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36306934824673002657616595 54460402237009503986424893)
    ·
      refine ⟨20422650838878563994909335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54460402237009503986424893 20422650838878563994909335)
      ·
        refine ⟨30633976258317845992364003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20422650838878563994909335 30633976258317845992364003)
        ·
          refine ⟨45950964387476768988546005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30633976258317845992364003 45950964387476768988546005)
          ·
            refine ⟨1076975727831486773169047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45950964387476768988546005 1076975727831486773169047)
            ·
              refine ⟨1615463591747230159753571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076975727831486773169047 1615463591747230159753571)
              ·
                refine ⟨2423195387620845239630357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615463591747230159753571 2423195387620845239630357)
                ·
                  refine ⟨113587283794727120607673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2423195387620845239630357 113587283794727120607673)
                  ·
                    rfl

theorem cell22_995447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 6].length) (baseStart_995447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995447 prefixEnd_995447 := by exact prefixLift 995447
  have htrace : WordTrace (prefixWord ++ tailWord_995447) baseStart_995447 baseEnd_995447 := by
    simpa [prefixWord, tailWord_995447, baseEnd_995447] using wordTrace_append hprefix tailTrace_995447
  have hstable : (prefixWord ++ tailWord_995447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995447).length < 2 ^ (prefixWord ++ tailWord_995447).sum := by decide
  have hdescent : baseEnd_995447 < baseStart_995447 := by decide
  rcases family_descends (prefixWord ++ tailWord_995447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995477 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_995477 : Nat := 118140960795 + 995477 * 2 ^ 59
def prefixEnd_995477 : Nat := 4983230072969 + 3 ^ 40 * 995477 * 2
def baseEnd_995477 : Nat := 340772120997271283572927

theorem tailTrace_995477 : CollatzResearch.WordTrace tailWord_995477 prefixEnd_995477 340772120997271283572927 := by
  unfold tailWord_995477
  simp only [CollatzResearch.WordTrace]
  refine ⟨36308029014564317781208685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24205352676376211854139123 36308029014564317781208685)
  ·
    refine ⟨13615510880461619167953257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36308029014564317781208685 13615510880461619167953257)
    ·
      refine ⟨10211633160346214375964943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13615510880461619167953257 10211633160346214375964943)
      ·
        refine ⟨15317449740519321563947415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10211633160346214375964943 15317449740519321563947415)
        ·
          refine ⟨22976174610778982345921123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15317449740519321563947415 22976174610778982345921123)
          ·
            refine ⟨34464261916168473518881685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22976174610778982345921123 34464261916168473518881685)
            ·
              refine ⟨1615512277320397196197579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34464261916168473518881685 1615512277320397196197579)
              ·
                refine ⟨2423268415980595794296369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615512277320397196197579 2423268415980595794296369)
                ·
                  refine ⟨1817451311985446845722277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2423268415980595794296369 1817451311985446845722277)
                  ·
                    refine ⟨340772120997271283572927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1817451311985446845722277 340772120997271283572927)
                    ·
                      rfl

theorem cell22_995477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_995477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995477 prefixEnd_995477 := by exact prefixLift 995477
  have htrace : WordTrace (prefixWord ++ tailWord_995477) baseStart_995477 baseEnd_995477 := by
    simpa [prefixWord, tailWord_995477, baseEnd_995477] using wordTrace_append hprefix tailTrace_995477
  have hstable : (prefixWord ++ tailWord_995477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995477).length < 2 ^ (prefixWord ++ tailWord_995477).sum := by decide
  have hdescent : baseEnd_995477 < baseStart_995477 := by decide
  rcases family_descends (prefixWord ++ tailWord_995477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995492 : List Nat := [2, 3, 1, 2, 5, 9]
def baseStart_995492 : Nat := 118140960795 + 995492 * 2 ^ 59
def prefixEnd_995492 : Nat := 4983230072969 + 3 ^ 40 * 995492 * 2
def baseEnd_995492 : Nat := 4207126614861928943801

theorem tailTrace_995492 : CollatzResearch.WordTrace tailWord_995492 prefixEnd_995492 4207126614861928943801 := by
  unfold tailWord_995492
  simp only [CollatzResearch.WordTrace]
  refine ⟨18154288054754987671502365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24205717406339983562003153 18154288054754987671502365)
  ·
    refine ⟨6807858020533120376813387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18154288054754987671502365 6807858020533120376813387)
    ·
      refine ⟨10211787030799680565220081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6807858020533120376813387 10211787030799680565220081)
      ·
        refine ⟨7658840273099760423915061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10211787030799680565220081 7658840273099760423915061)
        ·
          refine ⟨718016275603102539742037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7658840273099760423915061 718016275603102539742037)
          ·
            refine ⟨4207126614861928943801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 718016275603102539742037 4207126614861928943801)
            ·
              rfl

theorem cell22_995492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 9].length) (baseStart_995492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995492 prefixEnd_995492 := by exact prefixLift 995492
  have htrace : WordTrace (prefixWord ++ tailWord_995492) baseStart_995492 baseEnd_995492 := by
    simpa [prefixWord, tailWord_995492, baseEnd_995492] using wordTrace_append hprefix tailTrace_995492
  have hstable : (prefixWord ++ tailWord_995492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995492).length < 2 ^ (prefixWord ++ tailWord_995492).sum := by decide
  have hdescent : baseEnd_995492 < baseStart_995492 := by decide
  rcases family_descends (prefixWord ++ tailWord_995492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995507 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 3, 3]
def baseStart_995507 : Nat := 118140960795 + 995507 * 2 ^ 59
def prefixEnd_995507 : Nat := 4983230072969 + 3 ^ 40 * 995507 * 2
def baseEnd_995507 : Nat := 340782390610361205322835

theorem tailTrace_995507 : CollatzResearch.WordTrace tailWord_995507 prefixEnd_995507 340782390610361205322835 := by
  unfold tailWord_995507
  simp only [CollatzResearch.WordTrace]
  refine ⟨36309123204455632904800775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24206082136303755269867183 36309123204455632904800775)
  ·
    refine ⟨54463684806683449357201163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36309123204455632904800775 54463684806683449357201163)
    ·
      refine ⟨81695527210025174035801745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54463684806683449357201163 81695527210025174035801745)
      ·
        refine ⟨61271645407518880526851309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81695527210025174035801745 61271645407518880526851309)
        ·
          refine ⟨22976867027819580197569241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61271645407518880526851309 22976867027819580197569241)
          ·
            refine ⟨17232650270864685148176931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22976867027819580197569241 17232650270864685148176931)
            ·
              refine ⟨25848975406297027722265397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17232650270864685148176931 25848975406297027722265397)
              ·
                refine ⟨2423341444340346348962381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25848975406297027722265397 2423341444340346348962381)
                ·
                  refine ⟨908753041627629880860893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2423341444340346348962381 908753041627629880860893)
                  ·
                    refine ⟨340782390610361205322835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 908753041627629880860893 340782390610361205322835)
                    ·
                      rfl

theorem cell22_995507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 3].length) (baseStart_995507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995507 prefixEnd_995507 := by exact prefixLift 995507
  have htrace : WordTrace (prefixWord ++ tailWord_995507) baseStart_995507 baseEnd_995507 := by
    simpa [prefixWord, tailWord_995507, baseEnd_995507] using wordTrace_append hprefix tailTrace_995507
  have hstable : (prefixWord ++ tailWord_995507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995507).length < 2 ^ (prefixWord ++ tailWord_995507).sum := by decide
  have hdescent : baseEnd_995507 < baseStart_995507 := by decide
  rcases family_descends (prefixWord ++ tailWord_995507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995524 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_995524 : Nat := 118140960795 + 995524 * 2 ^ 59
def prefixEnd_995524 : Nat := 4983230072969 + 3 ^ 40 * 995524 * 2
def baseEnd_995524 : Nat := 340788210057778827647783

theorem tailTrace_995524 : CollatzResearch.WordTrace tailWord_995524 prefixEnd_995524 340788210057778827647783 := by
  unfold tailWord_995524
  simp only [CollatzResearch.WordTrace]
  refine ⟨18154871622697022404084813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24206495496929363205446417 18154871622697022404084813)
  ·
    refine ⟨6808076858511383401531805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18154871622697022404084813 6808076858511383401531805)
    ·
      refine ⟨2553028821941768775574427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6808076858511383401531805 2553028821941768775574427)
      ·
        refine ⟨3829543232912653163361641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553028821941768775574427 3829543232912653163361641)
        ·
          refine ⟨2872157424684489872521231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3829543232912653163361641 2872157424684489872521231)
          ·
            refine ⟨4308236137026734808781847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872157424684489872521231 4308236137026734808781847)
            ·
              refine ⟨6462354205540102213172771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308236137026734808781847 6462354205540102213172771)
              ·
                refine ⟨9693531308310153319759157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462354205540102213172771 9693531308310153319759157)
                ·
                  refine ⟨908768560154076873727421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9693531308310153319759157 908768560154076873727421)
                  ·
                    refine ⟨340788210057778827647783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 908768560154076873727421 340788210057778827647783)
                    ·
                      rfl

theorem cell22_995524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_995524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995524 prefixEnd_995524 := by exact prefixLift 995524
  have htrace : WordTrace (prefixWord ++ tailWord_995524) baseStart_995524 baseEnd_995524 := by
    simpa [prefixWord, tailWord_995524, baseEnd_995524] using wordTrace_append hprefix tailTrace_995524
  have hstable : (prefixWord ++ tailWord_995524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995524).length < 2 ^ (prefixWord ++ tailWord_995524).sum := by decide
  have hdescent : baseEnd_995524 < baseStart_995524 := by decide
  rcases family_descends (prefixWord ++ tailWord_995524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995535 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 1, 7]
def baseStart_995535 : Nat := 118140960795 + 995535 * 2 ^ 59
def prefixEnd_995535 : Nat := 4983230072969 + 3 ^ 40 * 995535 * 2
def baseEnd_995535 : Nat := 340791975582578465622749

theorem tailTrace_995535 : CollatzResearch.WordTrace tailWord_995535 prefixEnd_995535 340791975582578465622749 := by
  unfold tailWord_995535
  simp only [CollatzResearch.WordTrace]
  refine ⟨36310144448354193686820059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24206762965569462457880039 36310144448354193686820059)
  ·
    refine ⟨54465216672531290530230089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36310144448354193686820059 54465216672531290530230089)
    ·
      refine ⟨40848912504398467897672567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54465216672531290530230089 40848912504398467897672567)
      ·
        refine ⟨61273368756597701846508851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40848912504398467897672567 61273368756597701846508851)
        ·
          refine ⟨91910053134896552769763277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61273368756597701846508851 91910053134896552769763277)
          ·
            refine ⟨34466269925586207288661229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91910053134896552769763277 34466269925586207288661229)
            ·
              refine ⟨12924851222094827733247961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34466269925586207288661229 12924851222094827733247961)
              ·
                refine ⟨9693638416571120799935971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12924851222094827733247961 9693638416571120799935971)
                ·
                  refine ⟨14540457624856681199903957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693638416571120799935971 14540457624856681199903957)
                  ·
                    refine ⟨340791975582578465622749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14540457624856681199903957 340791975582578465622749)
                    ·
                      rfl

theorem cell22_995535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_995535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995535 prefixEnd_995535 := by exact prefixLift 995535
  have htrace : WordTrace (prefixWord ++ tailWord_995535) baseStart_995535 baseEnd_995535 := by
    simpa [prefixWord, tailWord_995535, baseEnd_995535] using wordTrace_append hprefix tailTrace_995535
  have hstable : (prefixWord ++ tailWord_995535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995535).length < 2 ^ (prefixWord ++ tailWord_995535).sum := by decide
  have hdescent : baseEnd_995535 < baseStart_995535 := by decide
  rcases family_descends (prefixWord ++ tailWord_995535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995631 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 2, 3]
def baseStart_995631 : Nat := 118140960795 + 995631 * 2 ^ 59
def prefixEnd_995631 : Nat := 4983230072969 + 3 ^ 40 * 995631 * 2
def baseEnd_995631 : Nat := 340824838344466215222455

theorem tailTrace_995631 : CollatzResearch.WordTrace tailWord_995631 prefixEnd_995631 340824838344466215222455 := by
  unfold tailWord_995631
  simp only [CollatzResearch.WordTrace]
  refine ⟨36313645856006402082314747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24209097237337601388209831 36313645856006402082314747)
  ·
    refine ⟨54470468784009603123472121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36313645856006402082314747 54470468784009603123472121)
    ·
      refine ⟨40852851588007202342604091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54470468784009603123472121 40852851588007202342604091)
      ·
        refine ⟨61279277382010803513906137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40852851588007202342604091 61279277382010803513906137)
        ·
          refine ⟨45959458036508102635429603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61279277382010803513906137 45959458036508102635429603)
          ·
            refine ⟨68939187054762153953144405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45959458036508102635429603 68939187054762153953144405)
            ·
              refine ⟨807881098297993991638411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 68939187054762153953144405 807881098297993991638411)
              ·
                refine ⟨1211821647446990987457617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807881098297993991638411 1211821647446990987457617)
                ·
                  refine ⟨908866235585243240593213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1211821647446990987457617 908866235585243240593213)
                  ·
                    refine ⟨340824838344466215222455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 908866235585243240593213 340824838344466215222455)
                    ·
                      rfl

theorem cell22_995631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 3].length) (baseStart_995631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995631 prefixEnd_995631 := by exact prefixLift 995631
  have htrace : WordTrace (prefixWord ++ tailWord_995631) baseStart_995631 baseEnd_995631 := by
    simpa [prefixWord, tailWord_995631, baseEnd_995631] using wordTrace_append hprefix tailTrace_995631
  have hstable : (prefixWord ++ tailWord_995631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995631).length < 2 ^ (prefixWord ++ tailWord_995631).sum := by decide
  have hdescent : baseEnd_995631 < baseStart_995631 := by decide
  rcases family_descends (prefixWord ++ tailWord_995631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995646 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_995646 : Nat := 118140960795 + 995646 * 2 ^ 59
def prefixEnd_995646 : Nat := 4983230072969 + 3 ^ 40 * 995646 * 2
def baseEnd_995646 : Nat := 340829973151011176097409

theorem tailTrace_995646 : CollatzResearch.WordTrace tailWord_995646 prefixEnd_995646 340829973151011176097409 := by
  unfold tailWord_995646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539274118869007455513849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24209461967301373096073861 4539274118869007455513849)
  ·
    refine ⟨3404455589151755591635387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4539274118869007455513849 3404455589151755591635387)
    ·
      refine ⟨5106683383727633387453081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404455589151755591635387 5106683383727633387453081)
      ·
        refine ⟨3830012537795725040589811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5106683383727633387453081 3830012537795725040589811)
        ·
          refine ⟨5745018806693587560884717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830012537795725040589811 5745018806693587560884717)
          ·
            refine ⟨2154382052510095335331769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5745018806693587560884717 2154382052510095335331769)
            ·
              refine ⟨1615786539382571501498827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154382052510095335331769 1615786539382571501498827)
              ·
                refine ⟨2423679809073857252248241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615786539382571501498827 2423679809073857252248241)
                ·
                  refine ⟨1817759856805392939186181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2423679809073857252248241 1817759856805392939186181)
                  ·
                    refine ⟨340829973151011176097409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1817759856805392939186181 340829973151011176097409)
                    ·
                      rfl

theorem cell22_995646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_995646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995646 prefixEnd_995646 := by exact prefixLift 995646
  have htrace : WordTrace (prefixWord ++ tailWord_995646) baseStart_995646 baseEnd_995646 := by
    simpa [prefixWord, tailWord_995646, baseEnd_995646] using wordTrace_append hprefix tailTrace_995646
  have hstable : (prefixWord ++ tailWord_995646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995646).length < 2 ^ (prefixWord ++ tailWord_995646).sum := by decide
  have hdescent : baseEnd_995646 < baseStart_995646 := by decide
  rcases family_descends (prefixWord ++ tailWord_995646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995717 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 10]
def baseStart_995717 : Nat := 118140960795 + 995717 * 2 ^ 59
def prefixEnd_995717 : Nat := 4983230072969 + 3 ^ 40 * 995717 * 2
def baseEnd_995717 : Nat := 113618092633996885857397

theorem tailTrace_995717 : CollatzResearch.WordTrace tailWord_995717 prefixEnd_995717 113618092633996885857397 := by
  unfold tailWord_995717
  simp only [CollatzResearch.WordTrace]
  refine ⟨36316782533694838769945405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24211188355796559179963603 36316782533694838769945405)
  ·
    refine ⟨13618793450135564538729527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36316782533694838769945405 13618793450135564538729527)
    ·
      refine ⟨20428190175203346808094291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618793450135564538729527 20428190175203346808094291)
      ·
        refine ⟨30642285262805020212141437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20428190175203346808094291 30642285262805020212141437)
        ·
          refine ⟨11490856973551882579553039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30642285262805020212141437 11490856973551882579553039)
          ·
            refine ⟨17236285460327823869329559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11490856973551882579553039 17236285460327823869329559)
            ·
              refine ⟨25854428190491735803994339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17236285460327823869329559 25854428190491735803994339)
              ·
                refine ⟨38781642285737603705991509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25854428190491735803994339 38781642285737603705991509)
                ·
                  refine ⟨113618092633996885857397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 38781642285737603705991509 113618092633996885857397)
                  ·
                    rfl

theorem cell22_995717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_995717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995717 prefixEnd_995717 := by exact prefixLift 995717
  have htrace : WordTrace (prefixWord ++ tailWord_995717) baseStart_995717 baseEnd_995717 := by
    simpa [prefixWord, tailWord_995717, baseEnd_995717] using wordTrace_append hprefix tailTrace_995717
  have hstable : (prefixWord ++ tailWord_995717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995717).length < 2 ^ (prefixWord ++ tailWord_995717).sum := by decide
  have hdescent : baseEnd_995717 < baseStart_995717 := by decide
  rcases family_descends (prefixWord ++ tailWord_995717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995796 : List Nat := [2, 4, 1, 2, 2, 2, 2, 7]
def baseStart_995796 : Nat := 118140960795 + 995796 * 2 ^ 59
def prefixEnd_995796 : Nat := 4983230072969 + 3 ^ 40 * 995796 * 2
def baseEnd_995796 : Nat := 37875702357384531649661

theorem tailTrace_995796 : CollatzResearch.WordTrace tailWord_995796 prefixEnd_995796 37875702357384531649661 := by
  unfold tailWord_995796
  simp only [CollatzResearch.WordTrace]
  refine ⟨18159831950204317631035621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24213109266939090174714161 18159831950204317631035621)
  ·
    refine ⟨3404968490663309555819179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18159831950204317631035621 3404968490663309555819179)
    ·
      refine ⟨5107452735994964333728769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404968490663309555819179 5107452735994964333728769)
      ·
        refine ⟨3830589551996223250296577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5107452735994964333728769 3830589551996223250296577)
        ·
          refine ⟨2872942163997167437722433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3830589551996223250296577 2872942163997167437722433)
          ·
            refine ⟨2154706622997875578291825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2872942163997167437722433 2154706622997875578291825)
            ·
              refine ⟨1616029967248406683718869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154706622997875578291825 1616029967248406683718869)
              ·
                refine ⟨37875702357384531649661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1616029967248406683718869 37875702357384531649661)
                ·
                  rfl

theorem cell22_995796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 7].length) (baseStart_995796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995796 prefixEnd_995796 := by exact prefixLift 995796
  have htrace : WordTrace (prefixWord ++ tailWord_995796) baseStart_995796 baseEnd_995796 := by
    simpa [prefixWord, tailWord_995796, baseEnd_995796] using wordTrace_append hprefix tailTrace_995796
  have hstable : (prefixWord ++ tailWord_995796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995796).length < 2 ^ (prefixWord ++ tailWord_995796).sum := by decide
  have hdescent : baseEnd_995796 < baseStart_995796 := by decide
  rcases family_descends (prefixWord ++ tailWord_995796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995839 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 2, 5]
def baseStart_995839 : Nat := 118140960795 + 995839 * 2 ^ 59
def prefixEnd_995839 : Nat := 4983230072969 + 3 ^ 40 * 995839 * 2
def baseEnd_995839 : Nat := 340896040995223006021817

theorem tailTrace_995839 : CollatzResearch.WordTrace tailWord_995839 prefixEnd_995839 340896040995223006021817 := by
  unfold tailWord_995839
  simp only [CollatzResearch.WordTrace]
  refine ⟨36321232239252853605886571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24214154826168569070591047 36321232239252853605886571)
  ·
    refine ⟨54481848358879280408829857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36321232239252853605886571 54481848358879280408829857)
    ·
      refine ⟨40861386269159460306622393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54481848358879280408829857 40861386269159460306622393)
      ·
        refine ⟨30646039701869595229966795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40861386269159460306622393 30646039701869595229966795)
        ·
          refine ⟨45969059552804392844950193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30646039701869595229966795 45969059552804392844950193)
          ·
            refine ⟨34476794664603294633712645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45969059552804392844950193 34476794664603294633712645)
            ·
              refine ⟨6464398999613117743821121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34476794664603294633712645 6464398999613117743821121)
              ·
                refine ⟨4848299249709838307865841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6464398999613117743821121 4848299249709838307865841)
                ·
                  refine ⟨3636224437282378730899381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4848299249709838307865841 3636224437282378730899381)
                  ·
                    refine ⟨340896040995223006021817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3636224437282378730899381 340896040995223006021817)
                    ·
                      rfl

theorem cell22_995839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_995839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995839 prefixEnd_995839 := by exact prefixLift 995839
  have htrace : WordTrace (prefixWord ++ tailWord_995839) baseStart_995839 baseEnd_995839 := by
    simpa [prefixWord, tailWord_995839, baseEnd_995839] using wordTrace_append hprefix tailTrace_995839
  have hstable : (prefixWord ++ tailWord_995839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995839).length < 2 ^ (prefixWord ++ tailWord_995839).sum := by decide
  have hdescent : baseEnd_995839 < baseStart_995839 := by decide
  rcases family_descends (prefixWord ++ tailWord_995839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995841 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 5]
def baseStart_995841 : Nat := 118140960795 + 995841 * 2 ^ 59
def prefixEnd_995841 : Nat := 4983230072969 + 3 ^ 40 * 995841 * 2
def baseEnd_995841 : Nat := 113632241878698555823937

theorem tailTrace_995841 : CollatzResearch.WordTrace tailWord_995841 prefixEnd_995841 113632241878698555823937 := by
  unfold tailWord_995841
  simp only [CollatzResearch.WordTrace]
  refine ⟨36321305185245607947459377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24214203456830405298306251 36321305185245607947459377)
  ·
    refine ⟨27240978888934205960594533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36321305185245607947459377 27240978888934205960594533)
    ·
      refine ⟨5107683541675163617611475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27240978888934205960594533 5107683541675163617611475)
      ·
        refine ⟨7661525312512745426417213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5107683541675163617611475 7661525312512745426417213)
        ·
          refine ⟨2873071992192279534906455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7661525312512745426417213 2873071992192279534906455)
          ·
            refine ⟨4309607988288419302359683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873071992192279534906455 4309607988288419302359683)
            ·
              refine ⟨6464411982432628953539525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309607988288419302359683 6464411982432628953539525)
              ·
                refine ⟨1212077246706117928788661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6464411982432628953539525 1212077246706117928788661)
                ·
                  refine ⟨113632241878698555823937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1212077246706117928788661 113632241878698555823937)
                  ·
                    rfl

theorem cell22_995841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_995841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995841 prefixEnd_995841 := by exact prefixLift 995841
  have htrace : WordTrace (prefixWord ++ tailWord_995841) baseStart_995841 baseEnd_995841 := by
    simpa [prefixWord, tailWord_995841, baseEnd_995841] using wordTrace_append hprefix tailTrace_995841
  have hstable : (prefixWord ++ tailWord_995841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995841).length < 2 ^ (prefixWord ++ tailWord_995841).sum := by decide
  have hdescent : baseEnd_995841 < baseStart_995841 := by decide
  rcases family_descends (prefixWord ++ tailWord_995841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995845 : List Nat := [1, 3, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_995845 : Nat := 118140960795 + 995845 * 2 ^ 59
def prefixEnd_995845 : Nat := 4983230072969 + 3 ^ 40 * 995845 * 2
def baseEnd_995845 : Nat := 340898094917840990371799

theorem tailTrace_995845 : CollatzResearch.WordTrace tailWord_995845 prefixEnd_995845 340898094917840990371799 := by
  unfold tailWord_995845
  simp only [CollatzResearch.WordTrace]
  refine ⟨36321451077231116630604989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24214300718154077753736659 36321451077231116630604989)
  ·
    refine ⟨13620544153961668736476871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36321451077231116630604989 13620544153961668736476871)
    ·
      refine ⟨20430816230942503104715307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13620544153961668736476871 20430816230942503104715307)
      ·
        refine ⟨30646224346413754657072961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20430816230942503104715307 30646224346413754657072961)
        ·
          refine ⟨22984668259810315992804721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30646224346413754657072961 22984668259810315992804721)
          ·
            refine ⟨17238501194857736994603541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22984668259810315992804721 17238501194857736994603541)
            ·
              refine ⟨808054743508956421622041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17238501194857736994603541 808054743508956421622041)
              ·
                refine ⟨606041057631717316216531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808054743508956421622041 606041057631717316216531)
                ·
                  refine ⟨909061586447575974324797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606041057631717316216531 909061586447575974324797)
                  ·
                    refine ⟨340898094917840990371799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909061586447575974324797 340898094917840990371799)
                    ·
                      rfl

theorem cell22_995845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_995845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995845 prefixEnd_995845 := by exact prefixLift 995845
  have htrace : WordTrace (prefixWord ++ tailWord_995845) baseStart_995845 baseEnd_995845 := by
    simpa [prefixWord, tailWord_995845, baseEnd_995845] using wordTrace_append hprefix tailTrace_995845
  have hstable : (prefixWord ++ tailWord_995845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995845).length < 2 ^ (prefixWord ++ tailWord_995845).sum := by decide
  have hdescent : baseEnd_995845 < baseStart_995845 := by decide
  rcases family_descends (prefixWord ++ tailWord_995845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995871 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 1, 4]
def baseStart_995871 : Nat := 118140960795 + 995871 * 2 ^ 59
def prefixEnd_995871 : Nat := 4983230072969 + 3 ^ 40 * 995871 * 2
def baseEnd_995871 : Nat := 340906995249185589221719

theorem tailTrace_995871 : CollatzResearch.WordTrace tailWord_995871 prefixEnd_995871 340906995249185589221719 := by
  unfold tailWord_995871
  simp only [CollatzResearch.WordTrace]
  refine ⟨36322399375136923071051467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24214932916757948714034311 36322399375136923071051467)
  ·
    refine ⟨54483599062705384606577201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36322399375136923071051467 54483599062705384606577201)
    ·
      refine ⟨40862699297029038454932901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54483599062705384606577201 40862699297029038454932901)
      ·
        refine ⟨7661756118192944710299919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40862699297029038454932901 7661756118192944710299919)
        ·
          refine ⟨11492634177289417065449879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661756118192944710299919 11492634177289417065449879)
          ·
            refine ⟨17238951265934125598174819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492634177289417065449879 17238951265934125598174819)
            ·
              refine ⟨25858426898901188397262229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17238951265934125598174819 25858426898901188397262229)
              ·
                refine ⟨1212113760885993206121667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25858426898901188397262229 1212113760885993206121667)
                ·
                  refine ⟨1818170641328989809182501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212113760885993206121667 1818170641328989809182501)
                  ·
                    refine ⟨340906995249185589221719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1818170641328989809182501 340906995249185589221719)
                    ·
                      rfl

theorem cell22_995871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_995871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995871 prefixEnd_995871 := by exact prefixLift 995871
  have htrace : WordTrace (prefixWord ++ tailWord_995871) baseStart_995871 baseEnd_995871 := by
    simpa [prefixWord, tailWord_995871, baseEnd_995871] using wordTrace_append hprefix tailTrace_995871
  have hstable : (prefixWord ++ tailWord_995871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995871).length < 2 ^ (prefixWord ++ tailWord_995871).sum := by decide
  have hdescent : baseEnd_995871 < baseStart_995871 := by decide
  rcases family_descends (prefixWord ++ tailWord_995871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995879 : List Nat := [1, 1, 7, 2, 1, 1, 2, 3, 1, 3]
def baseStart_995879 : Nat := 118140960795 + 995879 * 2 ^ 59
def prefixEnd_995879 : Nat := 4983230072969 + 3 ^ 40 * 995879 * 2
def baseEnd_995879 : Nat := 340909733812676235021695

theorem tailTrace_995879 : CollatzResearch.WordTrace tailWord_995879 prefixEnd_995879 340909733812676235021695 := by
  unfold tailWord_995879
  simp only [CollatzResearch.WordTrace]
  refine ⟨36322691159107940437342691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24215127439405293624895127 36322691159107940437342691)
  ·
    refine ⟨54484036738661910656014037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36322691159107940437342691 54484036738661910656014037)
    ·
      refine ⟨1276969611062388531000329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 54484036738661910656014037 1276969611062388531000329)
      ·
        refine ⟨957727208296791398250247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1276969611062388531000329 957727208296791398250247)
        ·
          refine ⟨1436590812445187097375371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957727208296791398250247 1436590812445187097375371)
          ·
            refine ⟨2154886218667780646063057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436590812445187097375371 2154886218667780646063057)
            ·
              refine ⟨1616164664000835484547293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154886218667780646063057 1616164664000835484547293)
              ·
                refine ⟨606061749000313306705235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1616164664000835484547293 606061749000313306705235)
                ·
                  refine ⟨909092623500469960057853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606061749000313306705235 909092623500469960057853)
                  ·
                    refine ⟨340909733812676235021695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909092623500469960057853 340909733812676235021695)
                    ·
                      rfl

theorem cell22_995879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_995879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995879 prefixEnd_995879 := by exact prefixLift 995879
  have htrace : WordTrace (prefixWord ++ tailWord_995879) baseStart_995879 baseEnd_995879 := by
    simpa [prefixWord, tailWord_995879, baseEnd_995879] using wordTrace_append hprefix tailTrace_995879
  have hstable : (prefixWord ++ tailWord_995879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995879).length < 2 ^ (prefixWord ++ tailWord_995879).sum := by decide
  have hdescent : baseEnd_995879 < baseStart_995879 := by decide
  rcases family_descends (prefixWord ++ tailWord_995879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995888 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 1, 4]
def baseStart_995888 : Nat := 118140960795 + 995888 * 2 ^ 59
def prefixEnd_995888 : Nat := 4983230072969 + 3 ^ 40 * 995888 * 2
def baseEnd_995888 : Nat := 340912814696603211546667

theorem tailTrace_995888 : CollatzResearch.WordTrace tailWord_995888 prefixEnd_995888 340912814696603211546667 := by
  unfold tailWord_995888
  simp only [CollatzResearch.WordTrace]
  refine ⟨18161509708037667487210159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24215346277383556649613545 18161509708037667487210159)
  ·
    refine ⟨27242264562056501230815239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18161509708037667487210159 27242264562056501230815239)
    ·
      refine ⟨40863396843084751846222859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27242264562056501230815239 40863396843084751846222859)
      ·
        refine ⟨61295095264627127769334289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40863396843084751846222859 61295095264627127769334289)
        ·
          refine ⟨45971321448470345827000717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61295095264627127769334289 45971321448470345827000717)
          ·
            refine ⟨17239245543176379685125269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45971321448470345827000717 17239245543176379685125269)
            ·
              refine ⟨808089634836392797740247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17239245543176379685125269 808089634836392797740247)
              ·
                refine ⟨1212134452254589196610371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808089634836392797740247 1212134452254589196610371)
                ·
                  refine ⟨1818201678381883794915557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212134452254589196610371 1818201678381883794915557)
                  ·
                    refine ⟨340912814696603211546667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1818201678381883794915557 340912814696603211546667)
                    ·
                      rfl

theorem cell22_995888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 4].length) (baseStart_995888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995888 prefixEnd_995888 := by exact prefixLift 995888
  have htrace : WordTrace (prefixWord ++ tailWord_995888) baseStart_995888 baseEnd_995888 := by
    simpa [prefixWord, tailWord_995888, baseEnd_995888] using wordTrace_append hprefix tailTrace_995888
  have hstable : (prefixWord ++ tailWord_995888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995888).length < 2 ^ (prefixWord ++ tailWord_995888).sum := by decide
  have hdescent : baseEnd_995888 < baseStart_995888 := by decide
  rcases family_descends (prefixWord ++ tailWord_995888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995892 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 5]
def baseStart_995892 : Nat := 118140960795 + 995892 * 2 ^ 59
def prefixEnd_995892 : Nat := 4983230072969 + 3 ^ 40 * 995892 * 2
def baseEnd_995892 : Nat := 113638061326116178148885

theorem tailTrace_995892 : CollatzResearch.WordTrace tailWord_995892 prefixEnd_995892 113638061326116178148885 := by
  unfold tailWord_995892
  simp only [CollatzResearch.WordTrace]
  refine ⟨18161582654030421828782965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24215443538707229105043953 18161582654030421828782965)
  ·
    refine ⟨1702648373815352046448403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18161582654030421828782965 1702648373815352046448403)
    ·
      refine ⟨2553972560723028069672605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702648373815352046448403 2553972560723028069672605)
      ·
        refine ⟨957739710271135526127227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2553972560723028069672605 957739710271135526127227)
        ·
          refine ⟨1436609565406703289190841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957739710271135526127227 1436609565406703289190841)
          ·
            refine ⟨1077457174055027466893131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1436609565406703289190841 1077457174055027466893131)
            ·
              refine ⟨1616185761082541200339697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077457174055027466893131 1616185761082541200339697)
              ·
                refine ⟨1212139320811905900254773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616185761082541200339697 1212139320811905900254773)
                ·
                  refine ⟨113638061326116178148885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1212139320811905900254773 113638061326116178148885)
                  ·
                    rfl

theorem cell22_995892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_995892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995892 prefixEnd_995892 := by exact prefixLift 995892
  have htrace : WordTrace (prefixWord ++ tailWord_995892) baseStart_995892 baseEnd_995892 := by
    simpa [prefixWord, tailWord_995892, baseEnd_995892] using wordTrace_append hprefix tailTrace_995892
  have hstable : (prefixWord ++ tailWord_995892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995892).length < 2 ^ (prefixWord ++ tailWord_995892).sum := by decide
  have hdescent : baseEnd_995892 < baseStart_995892 := by decide
  rcases family_descends (prefixWord ++ tailWord_995892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995918 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_995918 : Nat := 118140960795 + 995918 * 2 ^ 59
def prefixEnd_995918 : Nat := 4983230072969 + 3 ^ 40 * 995918 * 2
def baseEnd_995918 : Nat := 340923084309693133296575

theorem tailTrace_995918 : CollatzResearch.WordTrace tailWord_995918 prefixEnd_995918 340923084309693133296575 := by
  unfold tailWord_995918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540514200745831262251551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24216075737311100065341605 4540514200745831262251551)
  ·
    refine ⟨6810771301118746893377327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4540514200745831262251551 6810771301118746893377327)
    ·
      refine ⟨10216156951678120340065991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6810771301118746893377327 10216156951678120340065991)
      ·
        refine ⟨15324235427517180510098987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10216156951678120340065991 15324235427517180510098987)
        ·
          refine ⟨22986353141275770765148481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15324235427517180510098987 22986353141275770765148481)
          ·
            refine ⟨17239764855956828073861361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22986353141275770765148481 17239764855956828073861361)
            ·
              refine ⟨12929823641967621055396021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17239764855956828073861361 12929823641967621055396021)
              ·
                refine ⟨1212170966434464473943377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12929823641967621055396021 1212170966434464473943377)
                ·
                  refine ⟨909128224825848355457533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1212170966434464473943377 909128224825848355457533)
                  ·
                    refine ⟨340923084309693133296575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909128224825848355457533 340923084309693133296575)
                    ·
                      rfl

theorem cell22_995918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_995918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_995918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_995918 prefixEnd_995918 := by exact prefixLift 995918
  have htrace : WordTrace (prefixWord ++ tailWord_995918) baseStart_995918 baseEnd_995918 := by
    simpa [prefixWord, tailWord_995918, baseEnd_995918] using wordTrace_append hprefix tailTrace_995918
  have hstable : (prefixWord ++ tailWord_995918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995918).length < 2 ^ (prefixWord ++ tailWord_995918).sum := by decide
  have hdescent : baseEnd_995918 < baseStart_995918 := by decide
  rcases family_descends (prefixWord ++ tailWord_995918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996014 : List Nat := [4, 1, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_996014 : Nat := 118140960795 + 996014 * 2 ^ 59
def prefixEnd_996014 : Nat := 4983230072969 + 3 ^ 40 * 996014 * 2
def baseEnd_996014 : Nat := 340955947071580882896281

theorem tailTrace_996014 : CollatzResearch.WordTrace tailWord_996014 prefixEnd_996014 340955947071580882896281 := by
  unfold tailWord_996014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540951876702357311688387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24218410009079238995671397 4540951876702357311688387)
  ·
    refine ⟨6811427815053535967532581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4540951876702357311688387 6811427815053535967532581)
    ·
      refine ⟨1277142715322537993912359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6811427815053535967532581 1277142715322537993912359)
      ·
        refine ⟨1915714072983806990868539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277142715322537993912359 1915714072983806990868539)
        ·
          refine ⟨2873571109475710486302809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915714072983806990868539 2873571109475710486302809)
          ·
            refine ⟨2155178332106782864727107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2873571109475710486302809 2155178332106782864727107)
            ·
              refine ⟨3232767498160174297090661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155178332106782864727107 3232767498160174297090661)
              ·
                refine ⟨606143905905032680704499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3232767498160174297090661 606143905905032680704499)
                ·
                  refine ⟨909215858857549021056749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606143905905032680704499 909215858857549021056749)
                  ·
                    refine ⟨340955947071580882896281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909215858857549021056749 340955947071580882896281)
                    ·
                      rfl

theorem cell22_996014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_996014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996014 prefixEnd_996014 := by exact prefixLift 996014
  have htrace : WordTrace (prefixWord ++ tailWord_996014) baseStart_996014 baseEnd_996014 := by
    simpa [prefixWord, tailWord_996014, baseEnd_996014] using wordTrace_append hprefix tailTrace_996014
  have hstable : (prefixWord ++ tailWord_996014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996014).length < 2 ^ (prefixWord ++ tailWord_996014).sum := by decide
  have hdescent : baseEnd_996014 < baseStart_996014 := by decide
  rcases family_descends (prefixWord ++ tailWord_996014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996055 : List Nat := [1, 1, 3, 2, 1, 5, 2, 3, 4]
def baseStart_996055 : Nat := 118140960795 + 996055 * 2 ^ 59
def prefixEnd_996055 : Nat := 4983230072969 + 3 ^ 40 * 996055 * 2
def baseEnd_996055 : Nat := 113656660736490147540385

theorem tailTrace_996055 : CollatzResearch.WordTrace tailWord_996055 prefixEnd_996055 113656660736490147540385 := by
  unfold tailWord_996055
  simp only [CollatzResearch.WordTrace]
  refine ⟨36329110406470322495749619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24219406937646881663833079 36329110406470322495749619)
  ·
    refine ⟨54493665609705483743624429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36329110406470322495749619 54493665609705483743624429)
    ·
      refine ⟨20435124603639556403859161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54493665609705483743624429 20435124603639556403859161)
      ·
        refine ⟨15326343452729667302894371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20435124603639556403859161 15326343452729667302894371)
        ·
          refine ⟨22989515179094500954341557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15326343452729667302894371 22989515179094500954341557)
          ·
            refine ⟨2155267048040109464469521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22989515179094500954341557 2155267048040109464469521)
            ·
              refine ⟨1616450286030082098352141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155267048040109464469521 1616450286030082098352141)
              ·
                refine ⟨606168857261280786882053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1616450286030082098352141 606168857261280786882053)
                ·
                  refine ⟨113656660736490147540385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 606168857261280786882053 113656660736490147540385)
                  ·
                    rfl

theorem cell22_996055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 4].length) (baseStart_996055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996055 prefixEnd_996055 := by exact prefixLift 996055
  have htrace : WordTrace (prefixWord ++ tailWord_996055) baseStart_996055 baseEnd_996055 := by
    simpa [prefixWord, tailWord_996055, baseEnd_996055] using wordTrace_append hprefix tailTrace_996055
  have hstable : (prefixWord ++ tailWord_996055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996055).length < 2 ^ (prefixWord ++ tailWord_996055).sum := by decide
  have hdescent : baseEnd_996055 < baseStart_996055 := by decide
  rcases family_descends (prefixWord ++ tailWord_996055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996111 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 9]
def baseStart_996111 : Nat := 118140960795 + 996111 * 2 ^ 59
def prefixEnd_996111 : Nat := 4983230072969 + 3 ^ 40 * 996111 * 2
def baseEnd_996111 : Nat := 113663050717968321073661

theorem tailTrace_996111 : CollatzResearch.WordTrace tailWord_996111 prefixEnd_996111 113663050717968321073661 := by
  unfold tailWord_996111
  simp only [CollatzResearch.WordTrace]
  refine ⟨36331152894267444059788187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24220768596178296039858791 36331152894267444059788187)
  ·
    refine ⟨54496729341401166089682281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36331152894267444059788187 54496729341401166089682281)
    ·
      refine ⟨40872547006050874567261711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54496729341401166089682281 40872547006050874567261711)
      ·
        refine ⟨61308820509076311850892567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40872547006050874567261711 61308820509076311850892567)
        ·
          refine ⟨91963230763614467776338851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61308820509076311850892567 91963230763614467776338851)
          ·
            refine ⟨137944846145421701664508277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91963230763614467776338851 137944846145421701664508277)
            ·
              refine ⟨12932329326133284531047651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137944846145421701664508277 12932329326133284531047651)
              ·
                refine ⟨19398493989199926796571477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12932329326133284531047651 19398493989199926796571477)
                ·
                  refine ⟨113663050717968321073661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19398493989199926796571477 113663050717968321073661)
                  ·
                    rfl

theorem cell22_996111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 9].length) (baseStart_996111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996111 prefixEnd_996111 := by exact prefixLift 996111
  have htrace : WordTrace (prefixWord ++ tailWord_996111) baseStart_996111 baseEnd_996111 := by
    simpa [prefixWord, tailWord_996111, baseEnd_996111] using wordTrace_append hprefix tailTrace_996111
  have hstable : (prefixWord ++ tailWord_996111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996111).length < 2 ^ (prefixWord ++ tailWord_996111).sum := by decide
  have hdescent : baseEnd_996111 < baseStart_996111 := by decide
  rcases family_descends (prefixWord ++ tailWord_996111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996128 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 7]
def baseStart_996128 : Nat := 118140960795 + 996128 * 2 ^ 59
def prefixEnd_996128 : Nat := 4983230072969 + 3 ^ 40 * 996128 * 2
def baseEnd_996128 : Nat := 113664990533774195181977

theorem tailTrace_996128 : CollatzResearch.WordTrace tailWord_996128 prefixEnd_996128 113664990533774195181977 := by
  unfold tailWord_996128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165886467602927981578519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24221181956803903975438025 18165886467602927981578519)
  ·
    refine ⟨27248829701404391972367779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18165886467602927981578519 27248829701404391972367779)
    ·
      refine ⟨40873244552106587958551669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27248829701404391972367779 40873244552106587958551669)
      ·
        refine ⟨3831866676759992621114219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40873244552106587958551669 3831866676759992621114219)
        ·
          refine ⟨5747800015139988931671329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831866676759992621114219 5747800015139988931671329)
          ·
            refine ⟨4310850011354991698753497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5747800015139988931671329 4310850011354991698753497)
            ·
              refine ⟨3233137508516243774065123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310850011354991698753497 3233137508516243774065123)
              ·
                refine ⟨4849706262774365661097685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233137508516243774065123 4849706262774365661097685)
                ·
                  refine ⟨113664990533774195181977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4849706262774365661097685 113664990533774195181977)
                  ·
                    rfl

theorem cell22_996128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_996128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996128 prefixEnd_996128 := by exact prefixLift 996128
  have htrace : WordTrace (prefixWord ++ tailWord_996128) baseStart_996128 baseEnd_996128 := by
    simpa [prefixWord, tailWord_996128, baseEnd_996128] using wordTrace_append hprefix tailTrace_996128
  have hstable : (prefixWord ++ tailWord_996128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996128).length < 2 ^ (prefixWord ++ tailWord_996128).sum := by decide
  have hdescent : baseEnd_996128 < baseStart_996128 := by decide
  rcases family_descends (prefixWord ++ tailWord_996128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996138 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_996138 : Nat := 118140960795 + 996138 * 2 ^ 59
def prefixEnd_996138 : Nat := 4983230072969 + 3 ^ 40 * 996138 * 2
def baseEnd_996138 : Nat := 340998394805685892795901

theorem tailTrace_996138 : CollatzResearch.WordTrace tailWord_996138 prefixEnd_996138 340998394805685892795901 := by
  unfold tailWord_996138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9083034416292406917755267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24221425110113085114014045 9083034416292406917755267)
  ·
    refine ⟨13624551624438610376632901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9083034416292406917755267 13624551624438610376632901)
    ·
      refine ⟨2554603429582239445618669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13624551624438610376632901 2554603429582239445618669)
      ·
        refine ⟨957976286093339792107001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2554603429582239445618669 957976286093339792107001)
        ·
          refine ⟨718482214570004844080251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957976286093339792107001 718482214570004844080251)
          ·
            refine ⟨1077723321855007266120377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718482214570004844080251 1077723321855007266120377)
            ·
              refine ⟨808292491391255449590283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077723321855007266120377 808292491391255449590283)
              ·
                refine ⟨1212438737086883174385425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808292491391255449590283 1212438737086883174385425)
                ·
                  refine ⟨909329052815162380789069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1212438737086883174385425 909329052815162380789069)
                  ·
                    refine ⟨340998394805685892795901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909329052815162380789069 340998394805685892795901)
                    ·
                      rfl

theorem cell22_996138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_996138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996138 prefixEnd_996138 := by exact prefixLift 996138
  have htrace : WordTrace (prefixWord ++ tailWord_996138) baseStart_996138 baseEnd_996138 := by
    simpa [prefixWord, tailWord_996138, baseEnd_996138] using wordTrace_append hprefix tailTrace_996138
  have hstable : (prefixWord ++ tailWord_996138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996138).length < 2 ^ (prefixWord ++ tailWord_996138).sum := by decide
  have hdescent : baseEnd_996138 < baseStart_996138 := by decide
  rcases family_descends (prefixWord ++ tailWord_996138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996203 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 4, 4]
def baseStart_996203 : Nat := 118140960795 + 996203 * 2 ^ 59
def prefixEnd_996203 : Nat := 4983230072969 + 3 ^ 40 * 996203 * 2
def baseEnd_996203 : Nat := 341020645634047389920701

theorem tailTrace_996203 : CollatzResearch.WordTrace tailWord_996203 prefixEnd_996203 341020645634047389920701 := by
  unfold tailWord_996203
  simp only [CollatzResearch.WordTrace]
  refine ⟨36334508409934143772137263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24223005606622762514758175 36334508409934143772137263)
  ·
    refine ⟨54501762614901215658205895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36334508409934143772137263 54501762614901215658205895)
    ·
      refine ⟨81752643922351823487308843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54501762614901215658205895 81752643922351823487308843)
      ·
        refine ⟨122628965883527735230963265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81752643922351823487308843 122628965883527735230963265)
        ·
          refine ⟨91971724412645801423222449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122628965883527735230963265 91971724412645801423222449)
          ·
            refine ⟨68978793309484351067416837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91971724412645801423222449 68978793309484351067416837)
            ·
              refine ⟨12933523745528315825140657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68978793309484351067416837 12933523745528315825140657)
              ·
                refine ⟨9700142809146236868855493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12933523745528315825140657 9700142809146236868855493)
                ·
                  refine ⟨1818776776714919412910405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9700142809146236868855493 1818776776714919412910405)
                  ·
                    refine ⟨341020645634047389920701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1818776776714919412910405 341020645634047389920701)
                    ·
                      rfl

theorem cell22_996203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 4].length) (baseStart_996203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996203 prefixEnd_996203 := by exact prefixLift 996203
  have htrace : WordTrace (prefixWord ++ tailWord_996203) baseStart_996203 baseEnd_996203 := by
    simpa [prefixWord, tailWord_996203, baseEnd_996203] using wordTrace_append hprefix tailTrace_996203
  have hstable : (prefixWord ++ tailWord_996203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996203).length < 2 ^ (prefixWord ++ tailWord_996203).sum := by decide
  have hdescent : baseEnd_996203 < baseStart_996203 := by decide
  rcases family_descends (prefixWord ++ tailWord_996203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996205 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_996205 : Nat := 118140960795 + 996205 * 2 ^ 59
def prefixEnd_996205 : Nat := 4983230072969 + 3 ^ 40 * 996205 * 2
def baseEnd_996205 : Nat := 341021330274920051370695

theorem tailTrace_996205 : CollatzResearch.WordTrace tailWord_996205 prefixEnd_996205 341021330274920051370695 := by
  unfold tailWord_996205
  simp only [CollatzResearch.WordTrace]
  refine ⟨36334581355926898113710069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24223054237284598742473379 36334581355926898113710069)
  ·
    refine ⟨3406367002118146698160319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36334581355926898113710069 3406367002118146698160319)
    ·
      refine ⟨5109550503177220047240479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406367002118146698160319 5109550503177220047240479)
      ·
        refine ⟨7664325754765830070860719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109550503177220047240479 7664325754765830070860719)
        ·
          refine ⟨11496488632148745106291079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664325754765830070860719 11496488632148745106291079)
          ·
            refine ⟨17244732948223117659436619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496488632148745106291079 17244732948223117659436619)
            ·
              refine ⟨25867099422334676489154929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17244732948223117659436619 25867099422334676489154929)
              ·
                refine ⟨19400324566751007366866197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25867099422334676489154929 19400324566751007366866197)
                ·
                  refine ⟨909390214066453470321853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19400324566751007366866197 909390214066453470321853)
                  ·
                    refine ⟨341021330274920051370695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909390214066453470321853 341021330274920051370695)
                    ·
                      rfl

theorem cell22_996205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_996205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996205 prefixEnd_996205 := by exact prefixLift 996205
  have htrace : WordTrace (prefixWord ++ tailWord_996205) baseStart_996205 baseEnd_996205 := by
    simpa [prefixWord, tailWord_996205, baseEnd_996205] using wordTrace_append hprefix tailTrace_996205
  have hstable : (prefixWord ++ tailWord_996205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996205).length < 2 ^ (prefixWord ++ tailWord_996205).sum := by decide
  have hdescent : baseEnd_996205 < baseStart_996205 := by decide
  rcases family_descends (prefixWord ++ tailWord_996205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996226 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_996226 : Nat := 118140960795 + 996226 * 2 ^ 59
def prefixEnd_996226 : Nat := 4983230072969 + 3 ^ 40 * 996226 * 2
def baseEnd_996226 : Nat := 341028519004082996595631

theorem tailTrace_996226 : CollatzResearch.WordTrace tailWord_996226 prefixEnd_996226 341028519004082996595631 := by
  unfold tailWord_996226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9083836822212704675056133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24223564859233879133483021 9083836822212704675056133)
  ·
    refine ⟨1703219404164882126573025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9083836822212704675056133 1703219404164882126573025)
    ·
      refine ⟨1277414553123661594929769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1703219404164882126573025 1277414553123661594929769)
      ·
        refine ⟨958060914842746196197327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1277414553123661594929769 958060914842746196197327)
        ·
          refine ⟨1437091372264119294295991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958060914842746196197327 1437091372264119294295991)
          ·
            refine ⟨2155637058396178941443987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437091372264119294295991 2155637058396178941443987)
            ·
              refine ⟨3233455587594268412165981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155637058396178941443987 3233455587594268412165981)
              ·
                refine ⟨1212545845347850654562243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3233455587594268412165981 1212545845347850654562243)
                ·
                  refine ⟨1818818768021775981843365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212545845347850654562243 1818818768021775981843365)
                  ·
                    refine ⟨341028519004082996595631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1818818768021775981843365 341028519004082996595631)
                    ·
                      rfl

theorem cell22_996226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_996226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996226 prefixEnd_996226 := by exact prefixLift 996226
  have htrace : WordTrace (prefixWord ++ tailWord_996226) baseStart_996226 baseEnd_996226 := by
    simpa [prefixWord, tailWord_996226, baseEnd_996226] using wordTrace_append hprefix tailTrace_996226
  have hstable : (prefixWord ++ tailWord_996226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996226).length < 2 ^ (prefixWord ++ tailWord_996226).sum := by decide
  have hdescent : baseEnd_996226 < baseStart_996226 := by decide
  rcases family_descends (prefixWord ++ tailWord_996226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996293 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_996293 : Nat := 118140960795 + 996293 * 2 ^ 59
def prefixEnd_996293 : Nat := 4983230072969 + 3 ^ 40 * 996293 * 2
def baseEnd_996293 : Nat := 341051454473317155170425

theorem tailTrace_996293 : CollatzResearch.WordTrace tailWord_996293 prefixEnd_996293 341051454473317155170425 := by
  unfold tailWord_996293
  simp only [CollatzResearch.WordTrace]
  refine ⟨36337790979608089142913533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24225193986405392761942355 36337790979608089142913533)
  ·
    refine ⟨13626671617353033428592575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36337790979608089142913533 13626671617353033428592575)
    ·
      refine ⟨20440007426029550142888863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13626671617353033428592575 20440007426029550142888863)
      ·
        refine ⟨30660011139044325214333295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20440007426029550142888863 30660011139044325214333295)
        ·
          refine ⟨45990016708566487821499943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30660011139044325214333295 45990016708566487821499943)
          ·
            refine ⟨68985025062849731732249915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45990016708566487821499943 68985025062849731732249915)
            ·
              refine ⟨103477537594274597598374873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68985025062849731732249915 103477537594274597598374873)
              ·
                refine ⟨77608153195705948198781155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103477537594274597598374873 77608153195705948198781155)
                ·
                  refine ⟨116412229793558922298171733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77608153195705948198781155 116412229793558922298171733)
                  ·
                    refine ⟨341051454473317155170425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 116412229793558922298171733 341051454473317155170425)
                    ·
                      rfl

theorem cell22_996293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_996293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996293 prefixEnd_996293 := by exact prefixLift 996293
  have htrace : WordTrace (prefixWord ++ tailWord_996293) baseStart_996293 baseEnd_996293 := by
    simpa [prefixWord, tailWord_996293, baseEnd_996293] using wordTrace_append hprefix tailTrace_996293
  have hstable : (prefixWord ++ tailWord_996293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996293).length < 2 ^ (prefixWord ++ tailWord_996293).sum := by decide
  have hdescent : baseEnd_996293 < baseStart_996293 := by decide
  rcases family_descends (prefixWord ++ tailWord_996293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996314 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_996314 : Nat := 118140960795 + 996314 * 2 ^ 59
def prefixEnd_996314 : Nat := 4983230072969 + 3 ^ 40 * 996314 * 2
def baseEnd_996314 : Nat := 113686214400826700131787

theorem tailTrace_996314 : CollatzResearch.WordTrace tailWord_996314 prefixEnd_996314 113686214400826700131787 := by
  unfold tailWord_996314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084639228133002432356999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24225704608354673152951997 9084639228133002432356999)
  ·
    refine ⟨13626958842199503648535499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9084639228133002432356999 13626958842199503648535499)
    ·
      refine ⟨20440438263299255472803249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13626958842199503648535499 20440438263299255472803249)
      ·
        refine ⟨15330328697474441604602437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20440438263299255472803249 15330328697474441604602437)
        ·
          refine ⟨2874436630776457800862957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15330328697474441604602437 2874436630776457800862957)
          ·
            refine ⟨1077913736541171675323609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2874436630776457800862957 1077913736541171675323609)
            ·
              refine ⟨808435302405878756492707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077913736541171675323609 808435302405878756492707)
              ·
                refine ⟨1212652953608818134739061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808435302405878756492707 1212652953608818134739061)
                ·
                  refine ⟨113686214400826700131787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1212652953608818134739061 113686214400826700131787)
                  ·
                    rfl

theorem cell22_996314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_996314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996314 prefixEnd_996314 := by exact prefixLift 996314
  have htrace : WordTrace (prefixWord ++ tailWord_996314) baseStart_996314 baseEnd_996314 := by
    simpa [prefixWord, tailWord_996314, baseEnd_996314] using wordTrace_append hprefix tailTrace_996314
  have hstable : (prefixWord ++ tailWord_996314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996314).length < 2 ^ (prefixWord ++ tailWord_996314).sum := by decide
  have hdescent : baseEnd_996314 < baseStart_996314 := by decide
  rcases family_descends (prefixWord ++ tailWord_996314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996327 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 3, 4]
def baseStart_996327 : Nat := 118140960795 + 996327 * 2 ^ 59
def prefixEnd_996327 : Nat := 4983230072969 + 3 ^ 40 * 996327 * 2
def baseEnd_996327 : Nat := 341063093368152399820321

theorem tailTrace_996327 : CollatzResearch.WordTrace tailWord_996327 prefixEnd_996327 341063093368152399820321 := by
  unfold tailWord_996327
  simp only [CollatzResearch.WordTrace]
  refine ⟨36339031061484912949651235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24226020707656608633100823 36339031061484912949651235)
  ·
    refine ⟨54508546592227369424476853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36339031061484912949651235 54508546592227369424476853)
    ·
      refine ⟨5110176243021315883544705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54508546592227369424476853 5110176243021315883544705)
      ·
        refine ⟨3832632182265986912658529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5110176243021315883544705 3832632182265986912658529)
        ·
          refine ⟨2874474136699490184493897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3832632182265986912658529 2874474136699490184493897)
          ·
            refine ⟨2155855602524617638370423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874474136699490184493897 2155855602524617638370423)
            ·
              refine ⟨3233783403786926457555635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155855602524617638370423 3233783403786926457555635)
              ·
                refine ⟨4850675105680389686333453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233783403786926457555635 4850675105680389686333453)
                ·
                  refine ⟨1819003164630146132375045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4850675105680389686333453 1819003164630146132375045)
                  ·
                    refine ⟨341063093368152399820321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1819003164630146132375045 341063093368152399820321)
                    ·
                      rfl

theorem cell22_996327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_996327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996327 prefixEnd_996327 := by exact prefixLift 996327
  have htrace : WordTrace (prefixWord ++ tailWord_996327) baseStart_996327 baseEnd_996327 := by
    simpa [prefixWord, tailWord_996327, baseEnd_996327] using wordTrace_append hprefix tailTrace_996327
  have hstable : (prefixWord ++ tailWord_996327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996327).length < 2 ^ (prefixWord ++ tailWord_996327).sum := by decide
  have hdescent : baseEnd_996327 < baseStart_996327 := by decide
  rcases family_descends (prefixWord ++ tailWord_996327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996387 : List Nat := [1, 1, 1, 4, 3, 3, 3, 6]
def baseStart_996387 : Nat := 118140960795 + 996387 * 2 ^ 59
def prefixEnd_996387 : Nat := 4983230072969 + 3 ^ 40 * 996387 * 2
def baseEnd_996387 : Nat := 37898181399370249257793

theorem tailTrace_996387 : CollatzResearch.WordTrace tailWord_996387 prefixEnd_996387 37898181399370249257793 := by
  unfold tailWord_996387
  simp only [CollatzResearch.WordTrace]
  refine ⟨36341219441267543196835415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24227479627511695464556943 36341219441267543196835415)
  ·
    refine ⟨54511829161901314795253123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36341219441267543196835415 54511829161901314795253123)
    ·
      refine ⟨81767743742851972192879685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54511829161901314795253123 81767743742851972192879685)
      ·
        refine ⟨15331451951784744786164941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81767743742851972192879685 15331451951784744786164941)
        ·
          refine ⟨5749294481919279294811853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15331451951784744786164941 5749294481919279294811853)
          ·
            refine ⟨2155985430719729735554445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5749294481919279294811853 2155985430719729735554445)
            ·
              refine ⟨808494536519898650832917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2155985430719729735554445 808494536519898650832917)
              ·
                refine ⟨37898181399370249257793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 808494536519898650832917 37898181399370249257793)
                ·
                  rfl

theorem cell22_996387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 6].length) (baseStart_996387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996387 prefixEnd_996387 := by exact prefixLift 996387
  have htrace : WordTrace (prefixWord ++ tailWord_996387) baseStart_996387 baseEnd_996387 := by
    simpa [prefixWord, tailWord_996387, baseEnd_996387] using wordTrace_append hprefix tailTrace_996387
  have hstable : (prefixWord ++ tailWord_996387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996387).length < 2 ^ (prefixWord ++ tailWord_996387).sum := by decide
  have hdescent : baseEnd_996387 < baseStart_996387 := by decide
  rcases family_descends (prefixWord ++ tailWord_996387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996402 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_996402 : Nat := 118140960795 + 996402 * 2 ^ 59
def prefixEnd_996402 : Nat := 4983230072969 + 3 ^ 40 * 996402 * 2
def baseEnd_996402 : Nat := 341088767400877204195091

theorem tailTrace_996402 : CollatzResearch.WordTrace tailWord_996402 prefixEnd_996402 341088767400877204195091 := by
  unfold tailWord_996402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9085441634053300189657865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24227844357475467172420973 9085441634053300189657865)
  ·
    refine ⟨6814081225539975142243399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9085441634053300189657865 6814081225539975142243399)
    ·
      refine ⟨10221121838309962713365099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6814081225539975142243399 10221121838309962713365099)
      ·
        refine ⟨15331682757464944070047649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10221121838309962713365099 15331682757464944070047649)
        ·
          refine ⟨11498762068098708052535737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15331682757464944070047649 11498762068098708052535737)
          ·
            refine ⟨8624071551074031039401803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11498762068098708052535737 8624071551074031039401803)
            ·
              refine ⟨12936107326611046559102705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624071551074031039401803 12936107326611046559102705)
              ·
                refine ⟨9702080494958284919327029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12936107326611046559102705 9702080494958284919327029)
                ·
                  refine ⟨909570046402339211186909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9702080494958284919327029 909570046402339211186909)
                  ·
                    refine ⟨341088767400877204195091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909570046402339211186909 341088767400877204195091)
                    ·
                      rfl

theorem cell22_996402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_996402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996402 prefixEnd_996402 := by exact prefixLift 996402
  have htrace : WordTrace (prefixWord ++ tailWord_996402) baseStart_996402 baseEnd_996402 := by
    simpa [prefixWord, tailWord_996402, baseEnd_996402] using wordTrace_append hprefix tailTrace_996402
  have hstable : (prefixWord ++ tailWord_996402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996402).length < 2 ^ (prefixWord ++ tailWord_996402).sum := by decide
  have hdescent : baseEnd_996402 < baseStart_996402 := by decide
  rcases family_descends (prefixWord ++ tailWord_996402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996419 : List Nat := [1, 1, 1, 3, 1, 2, 3, 6, 1, 3]
def baseStart_996419 : Nat := 118140960795 + 996419 * 2 ^ 59
def prefixEnd_996419 : Nat := 4983230072969 + 3 ^ 40 * 996419 * 2
def baseEnd_996419 : Nat := 341094586848294826520039

theorem tailTrace_996419 : CollatzResearch.WordTrace tailWord_996419 prefixEnd_996419 341094586848294826520039 := by
  unfold tailWord_996419
  simp only [CollatzResearch.WordTrace]
  refine ⟨36342386577151612662000311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24228257718101075108000207 36342386577151612662000311)
  ·
    refine ⟨54513579865727418993000467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36342386577151612662000311 54513579865727418993000467)
    ·
      refine ⟨81770369798591128489500701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54513579865727418993000467 81770369798591128489500701)
      ·
        refine ⟨30663888674471673183562763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81770369798591128489500701 30663888674471673183562763)
        ·
          refine ⟨45995833011707509775344145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30663888674471673183562763 45995833011707509775344145)
          ·
            refine ⟨34496874758780632331508109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45995833011707509775344145 34496874758780632331508109)
            ·
              refine ⟨12936328034542737124315541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34496874758780632331508109 12936328034542737124315541)
              ·
                refine ⟨606390376619190802702291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12936328034542737124315541 606390376619190802702291)
                ·
                  refine ⟨909585564928786204053437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606390376619190802702291 909585564928786204053437)
                  ·
                    refine ⟨341094586848294826520039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909585564928786204053437 341094586848294826520039)
                    ·
                      rfl

theorem cell22_996419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 3].length) (baseStart_996419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996419 prefixEnd_996419 := by exact prefixLift 996419
  have htrace : WordTrace (prefixWord ++ tailWord_996419) baseStart_996419 baseEnd_996419 := by
    simpa [prefixWord, tailWord_996419, baseEnd_996419] using wordTrace_append hprefix tailTrace_996419
  have hstable : (prefixWord ++ tailWord_996419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996419).length < 2 ^ (prefixWord ++ tailWord_996419).sum := by decide
  have hdescent : baseEnd_996419 < baseStart_996419 := by decide
  rcases family_descends (prefixWord ++ tailWord_996419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996438 : List Nat := [5, 2, 2, 1, 2, 2, 2, 6]
def baseStart_996438 : Nat := 118140960795 + 996438 * 2 ^ 59
def prefixEnd_996438 : Nat := 4983230072969 + 3 ^ 40 * 996438 * 2
def baseEnd_996438 : Nat := 37900121215176123366109

theorem tailTrace_996438 : CollatzResearch.WordTrace tailWord_996438 prefixEnd_996438 37900121215176123366109 := by
  unfold tailWord_996438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271442472755173681683873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24228719709388519271294645 2271442472755173681683873)
  ·
    refine ⟨1703581854566380261262905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2271442472755173681683873 1703581854566380261262905)
    ·
      refine ⟨1277686390924785195947179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1703581854566380261262905 1277686390924785195947179)
      ·
        refine ⟨1916529586387177793920769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277686390924785195947179 1916529586387177793920769)
        ·
          refine ⟨1437397189790383345440577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916529586387177793920769 1437397189790383345440577)
          ·
            refine ⟨1078047892342787509080433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1437397189790383345440577 1078047892342787509080433)
            ·
              refine ⟨808535919257090631810325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1078047892342787509080433 808535919257090631810325)
              ·
                refine ⟨37900121215176123366109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 808535919257090631810325 37900121215176123366109)
                ·
                  rfl

theorem cell22_996438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_996438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996438 prefixEnd_996438 := by exact prefixLift 996438
  have htrace : WordTrace (prefixWord ++ tailWord_996438) baseStart_996438 baseEnd_996438 := by
    simpa [prefixWord, tailWord_996438, baseEnd_996438] using wordTrace_append hprefix tailTrace_996438
  have hstable : (prefixWord ++ tailWord_996438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996438).length < 2 ^ (prefixWord ++ tailWord_996438).sum := by decide
  have hdescent : baseEnd_996438 < baseStart_996438 := by decide
  rcases family_descends (prefixWord ++ tailWord_996438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996554 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_996554 : Nat := 118140960795 + 996554 * 2 ^ 59
def prefixEnd_996554 : Nat := 4983230072969 + 3 ^ 40 * 996554 * 2
def baseEnd_996554 : Nat := 341140800107199474394625

theorem tailTrace_996554 : CollatzResearch.WordTrace tailWord_996554 prefixEnd_996554 341140800107199474394625 := by
  unfold tailWord_996554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9086827607915632679541179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24231540287775020478776477 9086827607915632679541179)
  ·
    refine ⟨13630241411873449019311769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9086827607915632679541179 13630241411873449019311769)
    ·
      refine ⟨10222681058905086764483827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13630241411873449019311769 10222681058905086764483827)
      ·
        refine ⟨15334021588357630146725741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10222681058905086764483827 15334021588357630146725741)
        ·
          refine ⟨5750258095634111305022153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15334021588357630146725741 5750258095634111305022153)
          ·
            refine ⟨4312693571725583478766615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5750258095634111305022153 4312693571725583478766615)
            ·
              refine ⟨6469040357588375218149923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312693571725583478766615 6469040357588375218149923)
              ·
                refine ⟨9703560536382562827224885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6469040357588375218149923 9703560536382562827224885)
                ·
                  refine ⟨909708800285865265052333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9703560536382562827224885 909708800285865265052333)
                  ·
                    refine ⟨341140800107199474394625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909708800285865265052333 341140800107199474394625)
                    ·
                      rfl

theorem cell22_996554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_996554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996554 prefixEnd_996554 := by exact prefixLift 996554
  have htrace : WordTrace (prefixWord ++ tailWord_996554) baseStart_996554 baseEnd_996554 := by
    simpa [prefixWord, tailWord_996554, baseEnd_996554] using wordTrace_append hprefix tailTrace_996554
  have hstable : (prefixWord ++ tailWord_996554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996554).length < 2 ^ (prefixWord ++ tailWord_996554).sum := by decide
  have hdescent : baseEnd_996554 < baseStart_996554 := by decide
  rcases family_descends (prefixWord ++ tailWord_996554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996558 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_996558 : Nat := 118140960795 + 996558 * 2 ^ 59
def prefixEnd_996558 : Nat := 4983230072969 + 3 ^ 40 * 996558 * 2
def baseEnd_996558 : Nat := 341142169388944797294613

theorem tailTrace_996558 : CollatzResearch.WordTrace tailWord_996558 prefixEnd_996558 341142169388944797294613 := by
  unfold tailWord_996558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4543432040456004925163791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24231637549098692934206885 4543432040456004925163791)
  ·
    refine ⟨6815148060684007387745687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4543432040456004925163791 6815148060684007387745687)
    ·
      refine ⟨10222722091026011081618531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6815148060684007387745687 10222722091026011081618531)
      ·
        refine ⟨15334083136539016622427797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10222722091026011081618531 15334083136539016622427797)
        ·
          refine ⟨718785147025266404176303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15334083136539016622427797 718785147025266404176303)
          ·
            refine ⟨1078177720537899606264455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718785147025266404176303 1078177720537899606264455)
            ·
              refine ⟨1617266580806849409396683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078177720537899606264455 1617266580806849409396683)
              ·
                refine ⟨2425899871210274114095025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617266580806849409396683 2425899871210274114095025)
                ·
                  refine ⟨1819424903407705585571269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2425899871210274114095025 1819424903407705585571269)
                  ·
                    refine ⟨341142169388944797294613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1819424903407705585571269 341142169388944797294613)
                    ·
                      rfl

theorem cell22_996558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_996558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996558 prefixEnd_996558 := by exact prefixLift 996558
  have htrace : WordTrace (prefixWord ++ tailWord_996558) baseStart_996558 baseEnd_996558 := by
    simpa [prefixWord, tailWord_996558, baseEnd_996558] using wordTrace_append hprefix tailTrace_996558
  have hstable : (prefixWord ++ tailWord_996558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996558).length < 2 ^ (prefixWord ++ tailWord_996558).sum := by decide
  have hdescent : baseEnd_996558 < baseStart_996558 := by decide
  rcases family_descends (prefixWord ++ tailWord_996558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996665 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 1, 4]
def baseStart_996665 : Nat := 118140960795 + 996665 * 2 ^ 59
def prefixEnd_996665 : Nat := 4983230072969 + 3 ^ 40 * 996665 * 2
def baseEnd_996665 : Nat := 341178797675632184869285

theorem tailTrace_996665 : CollatzResearch.WordTrace tailWord_996665 prefixEnd_996665 341178797675632184869285 := by
  unfold tailWord_996665
  simp only [CollatzResearch.WordTrace]
  refine ⟨36351358934260396675455449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24234239289506931116970299 36351358934260396675455449)
  ·
    refine ⟨27263519200695297506591587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36351358934260396675455449 27263519200695297506591587)
    ·
      refine ⟨40895278801042946259887381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27263519200695297506591587 40895278801042946259887381)
      ·
        refine ⟨1916966193798888105932221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40895278801042946259887381 1916966193798888105932221)
        ·
          refine ⟨718862322674583039724583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1916966193798888105932221 718862322674583039724583)
          ·
            refine ⟨1078293484011874559586875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718862322674583039724583 1078293484011874559586875)
            ·
              refine ⟨1617440226017811839380313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078293484011874559586875 1617440226017811839380313)
              ·
                refine ⟨1213080169513358879535235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617440226017811839380313 1213080169513358879535235)
                ·
                  refine ⟨1819620254270038319302853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213080169513358879535235 1819620254270038319302853)
                  ·
                    refine ⟨341178797675632184869285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1819620254270038319302853 341178797675632184869285)
                    ·
                      rfl

theorem cell22_996665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 4].length) (baseStart_996665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996665 prefixEnd_996665 := by exact prefixLift 996665
  have htrace : WordTrace (prefixWord ++ tailWord_996665) baseStart_996665 baseEnd_996665 := by
    simpa [prefixWord, tailWord_996665, baseEnd_996665] using wordTrace_append hprefix tailTrace_996665
  have hstable : (prefixWord ++ tailWord_996665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996665).length < 2 ^ (prefixWord ++ tailWord_996665).sum := by decide
  have hdescent : baseEnd_996665 < baseStart_996665 := by decide
  rcases family_descends (prefixWord ++ tailWord_996665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996704 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_996704 : Nat := 118140960795 + 996704 * 2 ^ 59
def prefixEnd_996704 : Nat := 4983230072969 + 3 ^ 40 * 996704 * 2
def baseEnd_996704 : Nat := 341192148172649083144165

theorem tailTrace_996704 : CollatzResearch.WordTrace tailWord_996704 prefixEnd_996704 341192148172649083144165 := by
  unfold tailWord_996704
  simp only [CollatzResearch.WordTrace]
  refine ⟨18176390690559553168062583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24235187587412737557416777 18176390690559553168062583)
  ·
    refine ⟨27264586035839329752093875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18176390690559553168062583 27264586035839329752093875)
    ·
      refine ⟨40896879053758994628140813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27264586035839329752093875 40896879053758994628140813)
      ·
        refine ⟨15336329645159622985552805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40896879053758994628140813 15336329645159622985552805)
        ·
          refine ⟨2875561808467429309791151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15336329645159622985552805 2875561808467429309791151)
          ·
            refine ⟨4313342712701143964686727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875561808467429309791151 4313342712701143964686727)
            ·
              refine ⟨6470014069051715947030091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313342712701143964686727 6470014069051715947030091)
              ·
                refine ⟨9705021103577573920545137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6470014069051715947030091 9705021103577573920545137)
                ·
                  refine ⟨7278765827683180440408853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9705021103577573920545137 7278765827683180440408853)
                  ·
                    refine ⟨341192148172649083144165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7278765827683180440408853 341192148172649083144165)
                    ·
                      rfl

theorem cell22_996704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_996704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996704 prefixEnd_996704 := by exact prefixLift 996704
  have htrace : WordTrace (prefixWord ++ tailWord_996704) baseStart_996704 baseEnd_996704 := by
    simpa [prefixWord, tailWord_996704, baseEnd_996704] using wordTrace_append hprefix tailTrace_996704
  have hstable : (prefixWord ++ tailWord_996704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996704).length < 2 ^ (prefixWord ++ tailWord_996704).sum := by decide
  have hdescent : baseEnd_996704 < baseStart_996704 := by decide
  rcases family_descends (prefixWord ++ tailWord_996704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996719 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 5]
def baseStart_996719 : Nat := 118140960795 + 996719 * 2 ^ 59
def prefixEnd_996719 : Nat := 4983230072969 + 3 ^ 40 * 996719 * 2
def baseEnd_996719 : Nat := 113732427659731348006373

theorem tailTrace_996719 : CollatzResearch.WordTrace tailWord_996719 prefixEnd_996719 113732427659731348006373 := by
  unfold tailWord_996719
  simp only [CollatzResearch.WordTrace]
  refine ⟨36353328476064763897921211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24235552317376509265280807 36353328476064763897921211)
  ·
    refine ⟨54529992714097145846881817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36353328476064763897921211 54529992714097145846881817)
    ·
      refine ⟨40897494535572859385161363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54529992714097145846881817 40897494535572859385161363)
      ·
        refine ⟨61346241803359289077742045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40897494535572859385161363 61346241803359289077742045)
        ·
          refine ⟨23004840676259733404153267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61346241803359289077742045 23004840676259733404153267)
          ·
            refine ⟨34507261014389600106229901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23004840676259733404153267 34507261014389600106229901)
            ·
              refine ⟨12940222880396100039836213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34507261014389600106229901 12940222880396100039836213)
              ·
                refine ⟨1213145895037134378734645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12940222880396100039836213 1213145895037134378734645)
                ·
                  refine ⟨113732427659731348006373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1213145895037134378734645 113732427659731348006373)
                  ·
                    rfl

theorem cell22_996719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 5].length) (baseStart_996719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996719 prefixEnd_996719 := by exact prefixLift 996719
  have htrace : WordTrace (prefixWord ++ tailWord_996719) baseStart_996719 baseEnd_996719 := by
    simpa [prefixWord, tailWord_996719, baseEnd_996719] using wordTrace_append hprefix tailTrace_996719
  have hstable : (prefixWord ++ tailWord_996719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996719).length < 2 ^ (prefixWord ++ tailWord_996719).sum := by decide
  have hdescent : baseEnd_996719 < baseStart_996719 := by decide
  rcases family_descends (prefixWord ++ tailWord_996719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996740 : List Nat := [2, 3, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_996740 : Nat := 118140960795 + 996740 * 2 ^ 59
def prefixEnd_996740 : Nat := 4983230072969 + 3 ^ 40 * 996740 * 2
def baseEnd_996740 : Nat := 341204471708356989244055

theorem tailTrace_996740 : CollatzResearch.WordTrace tailWord_996740 prefixEnd_996740 341204471708356989244055 := by
  unfold tailWord_996740
  simp only [CollatzResearch.WordTrace]
  refine ⟨18177047204494342242217837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24236062939325789656290449 18177047204494342242217837)
  ·
    refine ⟨6816392701685378340831689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18177047204494342242217837 6816392701685378340831689)
    ·
      refine ⟨5112294526264033755623767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6816392701685378340831689 5112294526264033755623767)
      ·
        refine ⟨7668441789396050633435651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5112294526264033755623767 7668441789396050633435651)
        ·
          refine ⟨11502662684094075950153477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668441789396050633435651 11502662684094075950153477)
          ·
            refine ⟨2156749253267639240653777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11502662684094075950153477 2156749253267639240653777)
            ·
              refine ⟨1617561939950729430490333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156749253267639240653777 1617561939950729430490333)
              ·
                refine ⟨606585727481523536433875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1617561939950729430490333 606585727481523536433875)
                ·
                  refine ⟨909878591222285304650813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606585727481523536433875 909878591222285304650813)
                  ·
                    refine ⟨341204471708356989244055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909878591222285304650813 341204471708356989244055)
                    ·
                      rfl

theorem cell22_996740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_996740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996740 prefixEnd_996740 := by exact prefixLift 996740
  have htrace : WordTrace (prefixWord ++ tailWord_996740) baseStart_996740 baseEnd_996740 := by
    simpa [prefixWord, tailWord_996740, baseEnd_996740] using wordTrace_append hprefix tailTrace_996740
  have hstable : (prefixWord ++ tailWord_996740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996740).length < 2 ^ (prefixWord ++ tailWord_996740).sum := by decide
  have hdescent : baseEnd_996740 < baseStart_996740 := by decide
  rcases family_descends (prefixWord ++ tailWord_996740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996826 : List Nat := [3, 1, 1, 2, 3, 3, 2, 7]
def baseStart_996826 : Nat := 118140960795 + 996826 * 2 ^ 59
def prefixEnd_996826 : Nat := 4983230072969 + 3 ^ 40 * 996826 * 2
def baseEnd_996826 : Nat := 37914879029542381288199

theorem tailTrace_996826 : CollatzResearch.WordTrace tailWord_996826 prefixEnd_996826 37914879029542381288199 := by
  unfold tailWord_996826
  simp only [CollatzResearch.WordTrace]
  refine ⟨9089307771669280293016583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24238154057784747448044221 9089307771669280293016583)
  ·
    refine ⟨13633961657503920439524875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9089307771669280293016583 13633961657503920439524875)
    ·
      refine ⟨20450942486255880659287313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13633961657503920439524875 20450942486255880659287313)
      ·
        refine ⟨15338206864691910494465485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20450942486255880659287313 15338206864691910494465485)
        ·
          refine ⟨5751827574259466435424557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15338206864691910494465485 5751827574259466435424557)
          ·
            refine ⟨2156935340347299913284209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5751827574259466435424557 2156935340347299913284209)
            ·
              refine ⟨1617701505260474934963157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156935340347299913284209 1617701505260474934963157)
              ·
                refine ⟨37914879029542381288199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1617701505260474934963157 37914879029542381288199)
                ·
                  rfl

theorem cell22_996826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_996826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996826 prefixEnd_996826 := by exact prefixLift 996826
  have htrace : WordTrace (prefixWord ++ tailWord_996826) baseStart_996826 baseEnd_996826 := by
    simpa [prefixWord, tailWord_996826, baseEnd_996826] using wordTrace_append hprefix tailTrace_996826
  have hstable : (prefixWord ++ tailWord_996826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996826).length < 2 ^ (prefixWord ++ tailWord_996826).sum := by decide
  have hdescent : baseEnd_996826 < baseStart_996826 := by decide
  rcases family_descends (prefixWord ++ tailWord_996826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996845 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_996845 : Nat := 118140960795 + 996845 * 2 ^ 59
def prefixEnd_996845 : Nat := 4983230072969 + 3 ^ 40 * 996845 * 2
def baseEnd_996845 : Nat := 341240415354171715368733

theorem tailTrace_996845 : CollatzResearch.WordTrace tailWord_996845 prefixEnd_996845 341240415354171715368733 := by
  unfold tailWord_996845
  simp only [CollatzResearch.WordTrace]
  refine ⟨36357924073608287417007989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24238616049072191611338659 36357924073608287417007989)
  ·
    refine ⟨3408555381900776945344499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36357924073608287417007989 3408555381900776945344499)
    ·
      refine ⟨5112833072851165418016749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3408555381900776945344499 5112833072851165418016749)
      ·
        refine ⟨1917312402319187031756281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5112833072851165418016749 1917312402319187031756281)
        ·
          refine ⟨1437984301739390273817211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1917312402319187031756281 1437984301739390273817211)
          ·
            refine ⟨2156976452609085410725817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437984301739390273817211 2156976452609085410725817)
            ·
              refine ⟨1617732339456814058044363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156976452609085410725817 1617732339456814058044363)
              ·
                refine ⟨2426598509185221087066545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617732339456814058044363 2426598509185221087066545)
                ·
                  refine ⟨1819948881888915815299909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2426598509185221087066545 1819948881888915815299909)
                  ·
                    refine ⟨341240415354171715368733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1819948881888915815299909 341240415354171715368733)
                    ·
                      rfl

theorem cell22_996845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_996845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996845 prefixEnd_996845 := by exact prefixLift 996845
  have htrace : WordTrace (prefixWord ++ tailWord_996845) baseStart_996845 baseEnd_996845 := by
    simpa [prefixWord, tailWord_996845, baseEnd_996845] using wordTrace_append hprefix tailTrace_996845
  have hstable : (prefixWord ++ tailWord_996845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996845).length < 2 ^ (prefixWord ++ tailWord_996845).sum := by decide
  have hdescent : baseEnd_996845 < baseStart_996845 := by decide
  rcases family_descends (prefixWord ++ tailWord_996845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996877 : List Nat := [1, 7, 1, 1, 2, 2, 1, 7]
def baseStart_996877 : Nat := 118140960795 + 996877 * 2 ^ 59
def prefixEnd_996877 : Nat := 4983230072969 + 3 ^ 40 * 996877 * 2
def baseEnd_996877 : Nat := 37916818845348255396515

theorem tailTrace_996877 : CollatzResearch.WordTrace tailWord_996877 prefixEnd_996877 37916818845348255396515 := by
  unfold tailWord_996877
  simp only [CollatzResearch.WordTrace]
  refine ⟨36359091209492356882172885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24239394139661571254781923 36359091209492356882172885)
  ·
    refine ⟨852166200222477114425927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36359091209492356882172885 852166200222477114425927)
    ·
      refine ⟨1278249300333715671638891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852166200222477114425927 1278249300333715671638891)
      ·
        refine ⟨1917373950500573507458337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278249300333715671638891 1917373950500573507458337)
        ·
          refine ⟨1438030462875430130593753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1917373950500573507458337 1438030462875430130593753)
          ·
            refine ⟨1078522847156572597945315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1438030462875430130593753 1078522847156572597945315)
            ·
              refine ⟨1617784270734858896917973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078522847156572597945315 1617784270734858896917973)
              ·
                refine ⟨37916818845348255396515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1617784270734858896917973 37916818845348255396515)
                ·
                  rfl

theorem cell22_996877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 7].length) (baseStart_996877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996877 prefixEnd_996877 := by exact prefixLift 996877
  have htrace : WordTrace (prefixWord ++ tailWord_996877) baseStart_996877 baseEnd_996877 := by
    simpa [prefixWord, tailWord_996877, baseEnd_996877] using wordTrace_append hprefix tailTrace_996877
  have hstable : (prefixWord ++ tailWord_996877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996877).length < 2 ^ (prefixWord ++ tailWord_996877).sum := by decide
  have hdescent : baseEnd_996877 < baseStart_996877 := by decide
  rcases family_descends (prefixWord ++ tailWord_996877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996894 : List Nat := [4, 3, 3, 1, 1, 1, 3, 6]
def baseStart_996894 : Nat := 118140960795 + 996894 * 2 ^ 59
def prefixEnd_996894 : Nat := 4983230072969 + 3 ^ 40 * 996894 * 2
def baseEnd_996894 : Nat := 37917465450616880099287

theorem tailTrace_996894 : CollatzResearch.WordTrace tailWord_996894 prefixEnd_996894 37917465450616880099287 := by
  unfold tailWord_996894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544963906303846098192717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24239807500287179190361157 4544963906303846098192717)
  ·
    refine ⟨1704361464863942286822269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4544963906303846098192717 1704361464863942286822269)
    ·
      refine ⟨639135549323978357558351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1704361464863942286822269 639135549323978357558351)
      ·
        refine ⟨958703323985967536337527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639135549323978357558351 958703323985967536337527)
        ·
          refine ⟨1438054985978951304506291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958703323985967536337527 1438054985978951304506291)
          ·
            refine ⟨2157082478968426956759437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438054985978951304506291 2157082478968426956759437)
            ·
              refine ⟨808905929613160108784789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2157082478968426956759437 808905929613160108784789)
              ·
                refine ⟨37917465450616880099287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 808905929613160108784789 37917465450616880099287)
                ·
                  rfl

theorem cell22_996894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_996894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996894 prefixEnd_996894 := by exact prefixLift 996894
  have htrace : WordTrace (prefixWord ++ tailWord_996894) baseStart_996894 baseEnd_996894 := by
    simpa [prefixWord, tailWord_996894, baseEnd_996894] using wordTrace_append hprefix tailTrace_996894
  have hstable : (prefixWord ++ tailWord_996894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996894).length < 2 ^ (prefixWord ++ tailWord_996894).sum := by decide
  have hdescent : baseEnd_996894 < baseStart_996894 := by decide
  rcases family_descends (prefixWord ++ tailWord_996894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996933 : List Nat := [1, 3, 1, 1, 1, 4, 1, 6, 4]
def baseStart_996933 : Nat := 118140960795 + 996933 * 2 ^ 59
def prefixEnd_996933 : Nat := 4983230072969 + 3 ^ 40 * 996933 * 2
def baseEnd_996933 : Nat := 113756846517522939722821

theorem tailTrace_996933 : CollatzResearch.WordTrace tailWord_996933 prefixEnd_996933 113756846517522939722821 := by
  unfold tailWord_996933
  simp only [CollatzResearch.WordTrace]
  refine ⟨36361133697289478446211453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24240755798192985630807635 36361133697289478446211453)
  ·
    refine ⟨13635425136483554417329295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36361133697289478446211453 13635425136483554417329295)
    ·
      refine ⟨20453137704725331625993943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13635425136483554417329295 20453137704725331625993943)
      ·
        refine ⟨30679706557087997438990915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20453137704725331625993943 30679706557087997438990915)
        ·
          refine ⟨46019559835631996158486373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30679706557087997438990915 46019559835631996158486373)
          ·
            refine ⟨8628667469180999279716195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46019559835631996158486373 8628667469180999279716195)
            ·
              refine ⟨12943001203771498919574293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8628667469180999279716195 12943001203771498919574293)
              ·
                refine ⟨606703181426789011855045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12943001203771498919574293 606703181426789011855045)
                ·
                  refine ⟨113756846517522939722821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 606703181426789011855045 113756846517522939722821)
                  ·
                    rfl

theorem cell22_996933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_996933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996933 prefixEnd_996933 := by exact prefixLift 996933
  have htrace : WordTrace (prefixWord ++ tailWord_996933) baseStart_996933 baseEnd_996933 := by
    simpa [prefixWord, tailWord_996933, baseEnd_996933] using wordTrace_append hprefix tailTrace_996933
  have hstable : (prefixWord ++ tailWord_996933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996933).length < 2 ^ (prefixWord ++ tailWord_996933).sum := by decide
  have hdescent : baseEnd_996933 < baseStart_996933 := by decide
  rcases family_descends (prefixWord ++ tailWord_996933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996961 : List Nat := [1, 2, 3, 1, 1, 3, 3, 8]
def baseStart_996961 : Nat := 118140960795 + 996961 * 2 ^ 59
def prefixEnd_996961 : Nat := 4983230072969 + 3 ^ 40 * 996961 * 2
def baseEnd_996961 : Nat := 37920013836087342163153

theorem tailTrace_996961 : CollatzResearch.WordTrace tailWord_996961 prefixEnd_996961 37920013836087342163153 := by
  unfold tailWord_996961
  simp only [CollatzResearch.WordTrace]
  refine ⟨36362154941188039228230737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24241436627458692818820491 36362154941188039228230737)
  ·
    refine ⟨27271616205891029421173053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36362154941188039228230737 27271616205891029421173053)
    ·
      refine ⟨10226856077209136032939895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27271616205891029421173053 10226856077209136032939895)
      ·
        refine ⟨15340284115813704049409843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10226856077209136032939895 15340284115813704049409843)
        ·
          refine ⟨23010426173720556074114765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15340284115813704049409843 23010426173720556074114765)
          ·
            refine ⟨8628909815145208527793037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23010426173720556074114765 8628909815145208527793037)
            ·
              refine ⟨3235841180679453197922389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8628909815145208527793037 3235841180679453197922389)
              ·
                refine ⟨37920013836087342163153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3235841180679453197922389 37920013836087342163153)
                ·
                  rfl

theorem cell22_996961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 8].length) (baseStart_996961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996961 prefixEnd_996961 := by exact prefixLift 996961
  have htrace : WordTrace (prefixWord ++ tailWord_996961) baseStart_996961 baseEnd_996961 := by
    simpa [prefixWord, tailWord_996961, baseEnd_996961] using wordTrace_append hprefix tailTrace_996961
  have hstable : (prefixWord ++ tailWord_996961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996961).length < 2 ^ (prefixWord ++ tailWord_996961).sum := by decide
  have hdescent : baseEnd_996961 < baseStart_996961 := by decide
  rcases family_descends (prefixWord ++ tailWord_996961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996978 : List Nat := [3, 2, 1, 2, 3, 3, 8]
def baseStart_996978 : Nat := 118140960795 + 996978 * 2 ^ 59
def prefixEnd_996978 : Nat := 4983230072969 + 3 ^ 40 * 996978 * 2
def baseEnd_996978 : Nat := 12640220147118655621975

theorem tailTrace_996978 : CollatzResearch.WordTrace tailWord_996978 prefixEnd_996978 12640220147118655621975 := by
  unfold tailWord_996978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9090693745531612782899897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24241849988084300754399725 9090693745531612782899897)
  ·
    refine ⟨6818020309148709587174923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9090693745531612782899897 6818020309148709587174923)
    ·
      refine ⟨10227030463723064380762385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6818020309148709587174923 10227030463723064380762385)
      ·
        refine ⟨7670272847792298285571789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10227030463723064380762385 7670272847792298285571789)
        ·
          refine ⟨2876352317922111857089421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7670272847792298285571789 2876352317922111857089421)
          ·
            refine ⟨1078632119220791946408533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2876352317922111857089421 1078632119220791946408533)
            ·
              refine ⟨12640220147118655621975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1078632119220791946408533 12640220147118655621975)
              ·
                rfl

theorem cell22_996978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 8].length) (baseStart_996978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_996978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_996978 prefixEnd_996978 := by exact prefixLift 996978
  have htrace : WordTrace (prefixWord ++ tailWord_996978) baseStart_996978 baseEnd_996978 := by
    simpa [prefixWord, tailWord_996978, baseEnd_996978] using wordTrace_append hprefix tailTrace_996978
  have hstable : (prefixWord ++ tailWord_996978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996978).length < 2 ^ (prefixWord ++ tailWord_996978).sum := by decide
  have hdescent : baseEnd_996978 < baseStart_996978 := by decide
  rcases family_descends (prefixWord ++ tailWord_996978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997051 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 10]
def baseStart_997051 : Nat := 118140960795 + 997051 * 2 ^ 59
def prefixEnd_997051 : Nat := 4983230072969 + 3 ^ 40 * 997051 * 2
def baseEnd_997051 : Nat := 113770311121351948239367

theorem tailTrace_997051 : CollatzResearch.WordTrace tailWord_997051 prefixEnd_997051 113770311121351948239367 := by
  unfold tailWord_997051
  simp only [CollatzResearch.WordTrace]
  refine ⟨36365437510861984599007007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24243625007241323066004671 36365437510861984599007007)
  ·
    refine ⟨54548156266292976898510511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36365437510861984599007007 54548156266292976898510511)
    ·
      refine ⟨81822234399439465347765767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54548156266292976898510511 81822234399439465347765767)
      ·
        refine ⟨122733351599159198021648651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81822234399439465347765767 122733351599159198021648651)
        ·
          refine ⟨184100027398738797032472977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122733351599159198021648651 184100027398738797032472977)
          ·
            refine ⟨138075020549054097774354733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184100027398738797032472977 138075020549054097774354733)
            ·
              refine ⟨51778132705895286665383025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138075020549054097774354733 51778132705895286665383025)
              ·
                refine ⟨38833599529421464999037269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51778132705895286665383025 38833599529421464999037269)
                ·
                  refine ⟨113770311121351948239367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 38833599529421464999037269 113770311121351948239367)
                  ·
                    rfl

theorem cell22_997051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 10].length) (baseStart_997051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997051 prefixEnd_997051 := by exact prefixLift 997051
  have htrace : WordTrace (prefixWord ++ tailWord_997051) baseStart_997051 baseEnd_997051 := by
    simpa [prefixWord, tailWord_997051, baseEnd_997051] using wordTrace_append hprefix tailTrace_997051
  have hstable : (prefixWord ++ tailWord_997051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997051).length < 2 ^ (prefixWord ++ tailWord_997051).sum := by decide
  have hdescent : baseEnd_997051 < baseStart_997051 := by decide
  rcases family_descends (prefixWord ++ tailWord_997051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997053 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_997053 : Nat := 118140960795 + 997053 * 2 ^ 59
def prefixEnd_997053 : Nat := 4983230072969 + 3 ^ 40 * 997053 * 2
def baseEnd_997053 : Nat := 341311618004928506168095

theorem tailTrace_997053 : CollatzResearch.WordTrace tailWord_997053 prefixEnd_997053 341311618004928506168095 := by
  unfold tailWord_997053
  simp only [CollatzResearch.WordTrace]
  refine ⟨36365510456854738940579813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24243673637903159293719875 36365510456854738940579813)
  ·
    refine ⟨6818533210660263551358715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36365510456854738940579813 6818533210660263551358715)
    ·
      refine ⟨10227799815990395327038073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6818533210660263551358715 10227799815990395327038073)
      ·
        refine ⟨7670849861992796495278555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10227799815990395327038073 7670849861992796495278555)
        ·
          refine ⟨11506274792989194742917833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670849861992796495278555 11506274792989194742917833)
          ·
            refine ⟨8629706094741896057188375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11506274792989194742917833 8629706094741896057188375)
            ·
              refine ⟨12944559142112844085782563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629706094741896057188375 12944559142112844085782563)
              ·
                refine ⟨19416838713169266128673845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12944559142112844085782563 19416838713169266128673845)
                ·
                  refine ⟨1820328629359618699563173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19416838713169266128673845 1820328629359618699563173)
                  ·
                    refine ⟨341311618004928506168095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1820328629359618699563173 341311618004928506168095)
                    ·
                      rfl

theorem cell22_997053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_997053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997053 prefixEnd_997053 := by exact prefixLift 997053
  have htrace : WordTrace (prefixWord ++ tailWord_997053) baseStart_997053 baseEnd_997053 := by
    simpa [prefixWord, tailWord_997053, baseEnd_997053] using wordTrace_append hprefix tailTrace_997053
  have hstable : (prefixWord ++ tailWord_997053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997053).length < 2 ^ (prefixWord ++ tailWord_997053).sum := by decide
  have hdescent : baseEnd_997053 < baseStart_997053 := by decide
  rcases family_descends (prefixWord ++ tailWord_997053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997070 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_997070 : Nat := 118140960795 + 997070 * 2 ^ 59
def prefixEnd_997070 : Nat := 4983230072969 + 3 ^ 40 * 997070 * 2
def baseEnd_997070 : Nat := 341317437452346128493043

theorem tailTrace_997070 : CollatzResearch.WordTrace tailWord_997070 prefixEnd_997070 341317437452346128493043 := by
  unfold tailWord_997070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545766312224143855493583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24244086998528767229299109 4545766312224143855493583)
  ·
    refine ⟨6818649468336215783240375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4545766312224143855493583 6818649468336215783240375)
    ·
      refine ⟨10227974202504323674860563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6818649468336215783240375 10227974202504323674860563)
      ·
        refine ⟨15341961303756485512290845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10227974202504323674860563 15341961303756485512290845)
        ·
          refine ⟨5753235488908682067109067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15341961303756485512290845 5753235488908682067109067)
          ·
            refine ⟨8629853233363023100663601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753235488908682067109067 8629853233363023100663601)
            ·
              refine ⟨6472389925022267325497701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8629853233363023100663601 6472389925022267325497701)
              ·
                refine ⟨1213573110941675123530819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6472389925022267325497701 1213573110941675123530819)
                ·
                  refine ⟨1820359666412512685296229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213573110941675123530819 1820359666412512685296229)
                  ·
                    refine ⟨341317437452346128493043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1820359666412512685296229 341317437452346128493043)
                    ·
                      rfl

theorem cell22_997070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_997070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997070 prefixEnd_997070 := by exact prefixLift 997070
  have htrace : WordTrace (prefixWord ++ tailWord_997070) baseStart_997070 baseEnd_997070 := by
    simpa [prefixWord, tailWord_997070, baseEnd_997070] using wordTrace_append hprefix tailTrace_997070
  have hstable : (prefixWord ++ tailWord_997070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997070).length < 2 ^ (prefixWord ++ tailWord_997070).sum := by decide
  have hdescent : baseEnd_997070 < baseStart_997070 := by decide
  rcases family_descends (prefixWord ++ tailWord_997070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997078 : List Nat := [5, 2, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_997078 : Nat := 118140960795 + 997078 * 2 ^ 59
def prefixEnd_997078 : Nat := 4983230072969 + 3 ^ 40 * 997078 * 2
def baseEnd_997078 : Nat := 341320176015836774293019

theorem tailTrace_997078 : CollatzResearch.WordTrace tailWord_997078 prefixEnd_997078 341320176015836774293019 := by
  unfold tailWord_997078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272901392610260513139993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24244281521176112140159925 2272901392610260513139993)
  ·
    refine ⟨1704676044457695384854995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2272901392610260513139993 1704676044457695384854995)
    ·
      refine ⟨2557014066686543077282493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1704676044457695384854995 2557014066686543077282493)
      ·
        refine ⟨958880275007453653980935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2557014066686543077282493 958880275007453653980935)
        ·
          refine ⟨1438320412511180480971403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958880275007453653980935 1438320412511180480971403)
          ·
            refine ⟨2157480618766770721457105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438320412511180480971403 2157480618766770721457105)
            ·
              refine ⟨1618110464075078041092829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157480618766770721457105 1618110464075078041092829)
              ·
                refine ⟨606791424028154265409811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1618110464075078041092829 606791424028154265409811)
                ·
                  refine ⟨910187136042231398114717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606791424028154265409811 910187136042231398114717)
                  ·
                    refine ⟨341320176015836774293019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 910187136042231398114717 341320176015836774293019)
                    ·
                      rfl

theorem cell22_997078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_997078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997078 prefixEnd_997078 := by exact prefixLift 997078
  have htrace : WordTrace (prefixWord ++ tailWord_997078) baseStart_997078 baseEnd_997078 := by
    simpa [prefixWord, tailWord_997078, baseEnd_997078] using wordTrace_append hprefix tailTrace_997078
  have hstable : (prefixWord ++ tailWord_997078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997078).length < 2 ^ (prefixWord ++ tailWord_997078).sum := by decide
  have hdescent : baseEnd_997078 < baseStart_997078 := by decide
  rcases family_descends (prefixWord ++ tailWord_997078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997128 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_997128 : Nat := 118140960795 + 997128 * 2 ^ 59
def prefixEnd_997128 : Nat := 4983230072969 + 3 ^ 40 * 997128 * 2
def baseEnd_997128 : Nat := 341337292037653310542865

theorem tailTrace_997128 : CollatzResearch.WordTrace tailWord_997128 prefixEnd_997128 341337292037653310542865 := by
  unfold tailWord_997128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18184122965791513374780019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24245497287722017833040025 18184122965791513374780019)
  ·
    refine ⟨27276184448687270062170029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18184122965791513374780019 27276184448687270062170029)
    ·
      refine ⟨10228569168257726273313761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27276184448687270062170029 10228569168257726273313761)
      ·
        refine ⟨7671426876193294704985321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10228569168257726273313761 7671426876193294704985321)
        ·
          refine ⟨5753570157144971028738991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7671426876193294704985321 5753570157144971028738991)
          ·
            refine ⟨8630355235717456543108487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753570157144971028738991 8630355235717456543108487)
            ·
              refine ⟨12945532853576184814662731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8630355235717456543108487 12945532853576184814662731)
              ·
                refine ⟨19418299280364277221994097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12945532853576184814662731 19418299280364277221994097)
                ·
                  refine ⟨14563724460273207916495573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19418299280364277221994097 14563724460273207916495573)
                  ·
                    refine ⟨341337292037653310542865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14563724460273207916495573 341337292037653310542865)
                    ·
                      rfl

theorem cell22_997128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_997128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997128 prefixEnd_997128 := by exact prefixLift 997128
  have htrace : WordTrace (prefixWord ++ tailWord_997128) baseStart_997128 baseEnd_997128 := by
    simpa [prefixWord, tailWord_997128, baseEnd_997128] using wordTrace_append hprefix tailTrace_997128
  have hstable : (prefixWord ++ tailWord_997128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997128).length < 2 ^ (prefixWord ++ tailWord_997128).sum := by decide
  have hdescent : baseEnd_997128 < baseStart_997128 := by decide
  rcases family_descends (prefixWord ++ tailWord_997128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997130 : List Nat := [3, 1, 2, 2, 1, 3, 4, 6]
def baseStart_997130 : Nat := 118140960795 + 997130 * 2 ^ 59
def prefixEnd_997130 : Nat := 4983230072969 + 3 ^ 40 * 997130 * 2
def baseEnd_997130 : Nat := 37926441853169552443651

theorem tailTrace_997130 : CollatzResearch.WordTrace tailWord_997130 prefixEnd_997130 37926441853169552443651 := by
  unfold tailWord_997130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092079719393945272783211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24245545918383854060755229 9092079719393945272783211)
  ·
    refine ⟨13638119579090917909174817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9092079719393945272783211 13638119579090917909174817)
    ·
      refine ⟨10228589684318188431881113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13638119579090917909174817 10228589684318188431881113)
      ·
        refine ⟨7671442263238641323910835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10228589684318188431881113 7671442263238641323910835)
        ·
          refine ⟨11507163394857961985866253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7671442263238641323910835 11507163394857961985866253)
          ·
            refine ⟨4315186273071735744699845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11507163394857961985866253 4315186273071735744699845)
            ·
              refine ⟨809097426200950452131221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4315186273071735744699845 809097426200950452131221)
              ·
                refine ⟨37926441853169552443651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 809097426200950452131221 37926441853169552443651)
                ·
                  rfl

theorem cell22_997130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_997130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997130 prefixEnd_997130 := by exact prefixLift 997130
  have htrace : WordTrace (prefixWord ++ tailWord_997130) baseStart_997130 baseEnd_997130 := by
    simpa [prefixWord, tailWord_997130, baseEnd_997130] using wordTrace_append hprefix tailTrace_997130
  have hstable : (prefixWord ++ tailWord_997130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997130).length < 2 ^ (prefixWord ++ tailWord_997130).sum := by decide
  have hdescent : baseEnd_997130 < baseStart_997130 := by decide
  rcases family_descends (prefixWord ++ tailWord_997130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997235 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 6, 3]
def baseStart_997235 : Nat := 118140960795 + 997235 * 2 ^ 59
def prefixEnd_997235 : Nat := 4983230072969 + 3 ^ 40 * 997235 * 2
def baseEnd_997235 : Nat := 341373920324340698117537

theorem tailTrace_997235 : CollatzResearch.WordTrace tailWord_997235 prefixEnd_997235 341373920324340698117537 := by
  unfold tailWord_997235
  simp only [CollatzResearch.WordTrace]
  refine ⟨36372148542195384023705159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24248099028130256015803439 36372148542195384023705159)
  ·
    refine ⟨54558222813293076035557739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36372148542195384023705159 54558222813293076035557739)
    ·
      refine ⟨81837334219939614053336609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54558222813293076035557739 81837334219939614053336609)
      ·
        refine ⟨61378000664954710540002457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81837334219939614053336609 61378000664954710540002457)
        ·
          refine ⟨46033500498716032905001843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61378000664954710540002457 46033500498716032905001843)
          ·
            refine ⟨69050250748074049357502765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46033500498716032905001843 69050250748074049357502765)
            ·
              refine ⟨25893844030527768509063537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69050250748074049357502765 25893844030527768509063537)
              ·
                refine ⟨19420383022895826381797653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25893844030527768509063537 19420383022895826381797653)
                ·
                  refine ⟨910330454198241861646765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19420383022895826381797653 910330454198241861646765)
                  ·
                    refine ⟨341373920324340698117537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 910330454198241861646765 341373920324340698117537)
                    ·
                      rfl

theorem cell22_997235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 3].length) (baseStart_997235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997235 prefixEnd_997235 := by exact prefixLift 997235
  have htrace : WordTrace (prefixWord ++ tailWord_997235) baseStart_997235 baseEnd_997235 := by
    simpa [prefixWord, tailWord_997235, baseEnd_997235] using wordTrace_append hprefix tailTrace_997235
  have hstable : (prefixWord ++ tailWord_997235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997235).length < 2 ^ (prefixWord ++ tailWord_997235).sum := by decide
  have hdescent : baseEnd_997235 < baseStart_997235 := by decide
  rcases family_descends (prefixWord ++ tailWord_997235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997256 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 1, 4]
def baseStart_997256 : Nat := 118140960795 + 997256 * 2 ^ 59
def prefixEnd_997256 : Nat := 4983230072969 + 3 ^ 40 * 997256 * 2
def baseEnd_997256 : Nat := 341381109053503643342473

theorem tailTrace_997256 : CollatzResearch.WordTrace tailWord_997256 prefixEnd_997256 341381109053503643342473 := by
  unfold tailWord_997256
  simp only [CollatzResearch.WordTrace]
  refine ⟨18186457237559652305109811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24248609650079536406813081 18186457237559652305109811)
  ·
    refine ⟨27279685856339478457664717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18186457237559652305109811 27279685856339478457664717)
    ·
      refine ⟨10229882196127304421624269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27279685856339478457664717 10229882196127304421624269)
      ·
        refine ⟨3836205823547739158109101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10229882196127304421624269 3836205823547739158109101)
        ·
          refine ⟨1438577183830402184290913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3836205823547739158109101 1438577183830402184290913)
          ·
            refine ⟨1078932887872801638218185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1438577183830402184290913 1078932887872801638218185)
            ·
              refine ⟨809199665904601228663639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1078932887872801638218185 809199665904601228663639)
              ·
                refine ⟨1213799498856901842995459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809199665904601228663639 1213799498856901842995459)
                ·
                  refine ⟨1820699248285352764493189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213799498856901842995459 1820699248285352764493189)
                  ·
                    refine ⟨341381109053503643342473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1820699248285352764493189 341381109053503643342473)
                    ·
                      rfl

theorem cell22_997256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_997256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997256 prefixEnd_997256 := by exact prefixLift 997256
  have htrace : WordTrace (prefixWord ++ tailWord_997256) baseStart_997256 baseEnd_997256 := by
    simpa [prefixWord, tailWord_997256, baseEnd_997256] using wordTrace_append hprefix tailTrace_997256
  have hstable : (prefixWord ++ tailWord_997256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997256).length < 2 ^ (prefixWord ++ tailWord_997256).sum := by decide
  have hdescent : baseEnd_997256 < baseStart_997256 := by decide
  rcases family_descends (prefixWord ++ tailWord_997256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997355 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 6]
def baseStart_997355 : Nat := 118140960795 + 997355 * 2 ^ 59
def prefixEnd_997355 : Nat := 4983230072969 + 3 ^ 40 * 997355 * 2
def baseEnd_997355 : Nat := 113804999592233461705723

theorem tailTrace_997355 : CollatzResearch.WordTrace tailWord_997355 prefixEnd_997355 113804999592233461705723 := by
  unfold tailWord_997355
  simp only [CollatzResearch.WordTrace]
  refine ⟨36376525301760644518073519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24251016867840429678715679 36376525301760644518073519)
  ·
    refine ⟨54564787952640966777110279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36376525301760644518073519 54564787952640966777110279)
    ·
      refine ⟨81847181928961450165665419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54564787952640966777110279 81847181928961450165665419)
      ·
        refine ⟨122770772893442175248498129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81847181928961450165665419 122770772893442175248498129)
        ·
          refine ⟨92078079670081631436373597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122770772893442175248498129 92078079670081631436373597)
          ·
            refine ⟨34529279876280611788640099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92078079670081631436373597 34529279876280611788640099)
            ·
              refine ⟨51793919814420917682960149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34529279876280611788640099 51793919814420917682960149)
              ·
                refine ⟨2427839991300980516388757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51793919814420917682960149 2427839991300980516388757)
                ·
                  refine ⟨113804999592233461705723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2427839991300980516388757 113804999592233461705723)
                  ·
                    rfl

theorem cell22_997355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 6].length) (baseStart_997355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997355 prefixEnd_997355 := by exact prefixLift 997355
  have htrace : WordTrace (prefixWord ++ tailWord_997355) baseStart_997355 baseEnd_997355 := by
    simpa [prefixWord, tailWord_997355, baseEnd_997355] using wordTrace_append hprefix tailTrace_997355
  have hstable : (prefixWord ++ tailWord_997355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997355).length < 2 ^ (prefixWord ++ tailWord_997355).sum := by decide
  have hdescent : baseEnd_997355 < baseStart_997355 := by decide
  rcases family_descends (prefixWord ++ tailWord_997355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997385 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_997385 : Nat := 118140960795 + 997385 * 2 ^ 59
def prefixEnd_997385 : Nat := 4983230072969 + 3 ^ 40 * 997385 * 2
def baseEnd_997385 : Nat := 341425268389790306867077

theorem tailTrace_997385 : CollatzResearch.WordTrace tailWord_997385 prefixEnd_997385 341425268389790306867077 := by
  unfold tailWord_997385
  simp only [CollatzResearch.WordTrace]
  refine ⟨36377619491651959641665609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24251746327767973094443739 36377619491651959641665609)
  ·
    refine ⟨27283214618738969731249207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36377619491651959641665609 27283214618738969731249207)
    ·
      refine ⟨40924821928108454596873811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27283214618738969731249207 40924821928108454596873811)
      ·
        refine ⟨61387232892162681895310717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40924821928108454596873811 61387232892162681895310717)
        ·
          refine ⟨23020212334561005710741519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61387232892162681895310717 23020212334561005710741519)
          ·
            refine ⟨34530318501841508566112279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23020212334561005710741519 34530318501841508566112279)
            ·
              refine ⟨51795477752762262849168419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34530318501841508566112279 51795477752762262849168419)
              ·
                refine ⟨77693216629143394273752629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51795477752762262849168419 77693216629143394273752629)
                ·
                  refine ⟨7283739058982193213164309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77693216629143394273752629 7283739058982193213164309)
                  ·
                    refine ⟨341425268389790306867077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7283739058982193213164309 341425268389790306867077)
                    ·
                      rfl

theorem cell22_997385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_997385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997385 prefixEnd_997385 := by exact prefixLift 997385
  have htrace : WordTrace (prefixWord ++ tailWord_997385) baseStart_997385 baseEnd_997385 := by
    simpa [prefixWord, tailWord_997385, baseEnd_997385] using wordTrace_append hprefix tailTrace_997385
  have hstable : (prefixWord ++ tailWord_997385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997385).length < 2 ^ (prefixWord ++ tailWord_997385).sum := by decide
  have hdescent : baseEnd_997385 < baseStart_997385 := by decide
  rcases family_descends (prefixWord ++ tailWord_997385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997404 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_997404 : Nat := 118140960795 + 997404 * 2 ^ 59
def prefixEnd_997404 : Nat := 4983230072969 + 3 ^ 40 * 997404 * 2
def baseEnd_997404 : Nat := 341431772478080590642019

theorem tailTrace_997404 : CollatzResearch.WordTrace tailWord_997404 prefixEnd_997404 341431772478080590642019 := by
  unfold tailWord_997404
  simp only [CollatzResearch.WordTrace]
  refine ⟨18189156239291562943303633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24252208319055417257738177 18189156239291562943303633)
  ·
    refine ⟨13641867179468672207477725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18189156239291562943303633 13641867179468672207477725)
    ·
      refine ⟨5115700192300752077804147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13641867179468672207477725 5115700192300752077804147)
      ·
        refine ⟨7673550288451128116706221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115700192300752077804147 7673550288451128116706221)
        ·
          refine ⟨2877581358169173043764833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7673550288451128116706221 2877581358169173043764833)
          ·
            refine ⟨2158186018626879782823625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2877581358169173043764833 2158186018626879782823625)
            ·
              refine ⟨1618639513970159837117719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158186018626879782823625 1618639513970159837117719)
              ·
                refine ⟨2427959270955239755676579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618639513970159837117719 2427959270955239755676579)
                ·
                  refine ⟨3641938906432859633514869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427959270955239755676579 3641938906432859633514869)
                  ·
                    refine ⟨341431772478080590642019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3641938906432859633514869 341431772478080590642019)
                    ·
                      rfl

theorem cell22_997404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_997404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997404 prefixEnd_997404 := by exact prefixLift 997404
  have htrace : WordTrace (prefixWord ++ tailWord_997404) baseStart_997404 baseEnd_997404 := by
    simpa [prefixWord, tailWord_997404, baseEnd_997404] using wordTrace_append hprefix tailTrace_997404
  have hstable : (prefixWord ++ tailWord_997404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997404).length < 2 ^ (prefixWord ++ tailWord_997404).sum := by decide
  have hdescent : baseEnd_997404 < baseStart_997404 := by decide
  rcases family_descends (prefixWord ++ tailWord_997404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997449 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 3, 3]
def baseStart_997449 : Nat := 118140960795 + 997449 * 2 ^ 59
def prefixEnd_997449 : Nat := 4983230072969 + 3 ^ 40 * 997449 * 2
def baseEnd_997449 : Nat := 341447176897715473266881

theorem tailTrace_997449 : CollatzResearch.WordTrace tailWord_997449 prefixEnd_997449 341447176897715473266881 := by
  unfold tailWord_997449
  simp only [CollatzResearch.WordTrace]
  refine ⟨36379953763420098571995401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24253302508946732381330267 36379953763420098571995401)
  ·
    refine ⟨27284965322565073928996551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36379953763420098571995401 27284965322565073928996551)
    ·
      refine ⟨40927447983847610893494827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27284965322565073928996551 40927447983847610893494827)
      ·
        refine ⟨61391171975771416340242241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40927447983847610893494827 61391171975771416340242241)
        ·
          refine ⟨46043378981828562255181681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61391171975771416340242241 46043378981828562255181681)
          ·
            refine ⟨34532534236371421691386261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46043378981828562255181681 34532534236371421691386261)
            ·
              refine ⟨1618712542329910391783731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34532534236371421691386261 1618712542329910391783731)
              ·
                refine ⟨2428068813494865587675597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618712542329910391783731 2428068813494865587675597)
                ·
                  refine ⟨910525805060574595378349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2428068813494865587675597 910525805060574595378349)
                  ·
                    refine ⟨341447176897715473266881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 910525805060574595378349 341447176897715473266881)
                    ·
                      rfl

theorem cell22_997449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_997449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997449 prefixEnd_997449 := by exact prefixLift 997449
  have htrace : WordTrace (prefixWord ++ tailWord_997449) baseStart_997449 baseEnd_997449 := by
    simpa [prefixWord, tailWord_997449, baseEnd_997449] using wordTrace_append hprefix tailTrace_997449
  have hstable : (prefixWord ++ tailWord_997449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997449).length < 2 ^ (prefixWord ++ tailWord_997449).sum := by decide
  have hdescent : baseEnd_997449 < baseStart_997449 := by decide
  rcases family_descends (prefixWord ++ tailWord_997449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997554 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_997554 : Nat := 118140960795 + 997554 * 2 ^ 59
def prefixEnd_997554 : Nat := 4983230072969 + 3 ^ 40 * 997554 * 2
def baseEnd_997554 : Nat := 341483120543530199391559

theorem tailTrace_997554 : CollatzResearch.WordTrace tailWord_997554 prefixEnd_997554 341483120543530199391559 := by
  unfold tailWord_997554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9095945857009925376141929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24255855618693134336378477 9095945857009925376141929)
  ·
    refine ⟨6821959392757444032106447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9095945857009925376141929 6821959392757444032106447)
    ·
      refine ⟨10232939089136166048159671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6821959392757444032106447 10232939089136166048159671)
      ·
        refine ⟨15349408633704249072239507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10232939089136166048159671 15349408633704249072239507)
        ·
          refine ⟨23024112950556373608359261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15349408633704249072239507 23024112950556373608359261)
          ·
            refine ⟨8634042356458640103134723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23024112950556373608359261 8634042356458640103134723)
            ·
              refine ⟨12951063534687960154702085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634042356458640103134723 12951063534687960154702085)
              ·
                refine ⟨2428324412753992529006641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12951063534687960154702085 2428324412753992529006641)
                ·
                  refine ⟨1821243309565494396754981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2428324412753992529006641 1821243309565494396754981)
                  ·
                    refine ⟨341483120543530199391559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1821243309565494396754981 341483120543530199391559)
                    ·
                      rfl

theorem cell22_997554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_997554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997554 prefixEnd_997554 := by exact prefixLift 997554
  have htrace : WordTrace (prefixWord ++ tailWord_997554) baseStart_997554 baseEnd_997554 := by
    simpa [prefixWord, tailWord_997554, baseEnd_997554] using wordTrace_append hprefix tailTrace_997554
  have hstable : (prefixWord ++ tailWord_997554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997554).length < 2 ^ (prefixWord ++ tailWord_997554).sum := by decide
  have hdescent : baseEnd_997554 < baseStart_997554 := by decide
  rcases family_descends (prefixWord ++ tailWord_997554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997567 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 2, 7]
def baseStart_997567 : Nat := 118140960795 + 997567 * 2 ^ 59
def prefixEnd_997567 : Nat := 4983230072969 + 3 ^ 40 * 997567 * 2
def baseEnd_997567 : Nat := 341487570709202498816519

theorem tailTrace_997567 : CollatzResearch.WordTrace tailWord_997567 prefixEnd_997567 341487570709202498816519 := by
  unfold tailWord_997567
  simp only [CollatzResearch.WordTrace]
  refine ⟨36384257576992604724790955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24256171717995069816527303 36384257576992604724790955)
  ·
    refine ⟨54576386365488907087186433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36384257576992604724790955 54576386365488907087186433)
    ·
      refine ⟨40932289774116680315389825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54576386365488907087186433 40932289774116680315389825)
      ·
        refine ⟨30699217330587510236542369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40932289774116680315389825 30699217330587510236542369)
        ·
          refine ⟨23024412997940632677406777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30699217330587510236542369 23024412997940632677406777)
          ·
            refine ⟨17268309748455474508055083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23024412997940632677406777 17268309748455474508055083)
            ·
              refine ⟨25902464622683211762082625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17268309748455474508055083 25902464622683211762082625)
              ·
                refine ⟨19426848467012408821561969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25902464622683211762082625 19426848467012408821561969)
                ·
                  refine ⟨14570136350259306616171477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19426848467012408821561969 14570136350259306616171477)
                  ·
                    refine ⟨341487570709202498816519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14570136350259306616171477 341487570709202498816519)
                    ·
                      rfl

theorem cell22_997567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_997567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997567 prefixEnd_997567 := by exact prefixLift 997567
  have htrace : WordTrace (prefixWord ++ tailWord_997567) baseStart_997567 baseEnd_997567 := by
    simpa [prefixWord, tailWord_997567, baseEnd_997567] using wordTrace_append hprefix tailTrace_997567
  have hstable : (prefixWord ++ tailWord_997567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997567).length < 2 ^ (prefixWord ++ tailWord_997567).sum := by decide
  have hdescent : baseEnd_997567 < baseStart_997567 := by decide
  rcases family_descends (prefixWord ++ tailWord_997567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997586 : List Nat := [3, 2, 2, 2, 1, 3, 3, 6]
def baseStart_997586 : Nat := 118140960795 + 997586 * 2 ^ 59
def prefixEnd_997586 : Nat := 4983230072969 + 3 ^ 40 * 997586 * 2
def baseEnd_997586 : Nat := 37943786088610309176829

theorem tailTrace_997586 : CollatzResearch.WordTrace tailWord_997586 prefixEnd_997586 37943786088610309176829 := by
  unfold tailWord_997586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096237640980942742433153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24256633709282513979821741 9096237640980942742433153)
  ·
    refine ⟨6822178230735707056824865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9096237640980942742433153 6822178230735707056824865)
    ·
      refine ⟨5116633673051780292618649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6822178230735707056824865 5116633673051780292618649)
      ·
        refine ⟨3837475254788835219463987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5116633673051780292618649 3837475254788835219463987)
        ·
          refine ⟨5756212882183252829195981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837475254788835219463987 5756212882183252829195981)
          ·
            refine ⟨2158579830818719810948493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5756212882183252829195981 2158579830818719810948493)
            ·
              refine ⟨809467436557019929105685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2158579830818719810948493 809467436557019929105685)
              ·
                refine ⟨37943786088610309176829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 809467436557019929105685 37943786088610309176829)
                ·
                  rfl

theorem cell22_997586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_997586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997586 prefixEnd_997586 := by exact prefixLift 997586
  have htrace : WordTrace (prefixWord ++ tailWord_997586) baseStart_997586 baseEnd_997586 := by
    simpa [prefixWord, tailWord_997586, baseEnd_997586] using wordTrace_append hprefix tailTrace_997586
  have hstable : (prefixWord ++ tailWord_997586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997586).length < 2 ^ (prefixWord ++ tailWord_997586).sum := by decide
  have hdescent : baseEnd_997586 < baseStart_997586 := by decide
  rcases family_descends (prefixWord ++ tailWord_997586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997618 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_997618 : Nat := 118140960795 + 997618 * 2 ^ 59
def prefixEnd_997618 : Nat := 4983230072969 + 3 ^ 40 * 997618 * 2
def baseEnd_997618 : Nat := 341505029051455365791363

theorem tailTrace_997618 : CollatzResearch.WordTrace tailWord_997618 prefixEnd_997618 341505029051455365791363 := by
  unfold tailWord_997618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096529424951960108724377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24257411799871893623265005 9096529424951960108724377)
  ·
    refine ⟨6822397068713970081543283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9096529424951960108724377 6822397068713970081543283)
    ·
      refine ⟨10233595603070955122314925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6822397068713970081543283 10233595603070955122314925)
      ·
        refine ⟨3837598351151608170868097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10233595603070955122314925 3837598351151608170868097)
        ·
          refine ⟨2878198763363706128151073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3837598351151608170868097 2878198763363706128151073)
          ·
            refine ⟨2158649072522779596113305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2878198763363706128151073 2158649072522779596113305)
            ·
              refine ⟨1618986804392084697084979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158649072522779596113305 1618986804392084697084979)
              ·
                refine ⟨2428480206588127045627469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618986804392084697084979 2428480206588127045627469)
                ·
                  refine ⟨910680077470547642110301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2428480206588127045627469 910680077470547642110301)
                  ·
                    refine ⟨341505029051455365791363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 910680077470547642110301 341505029051455365791363)
                    ·
                      rfl

theorem cell22_997618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_997618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997618 prefixEnd_997618 := by exact prefixLift 997618
  have htrace : WordTrace (prefixWord ++ tailWord_997618) baseStart_997618 baseEnd_997618 := by
    simpa [prefixWord, tailWord_997618, baseEnd_997618] using wordTrace_append hprefix tailTrace_997618
  have hstable : (prefixWord ++ tailWord_997618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997618).length < 2 ^ (prefixWord ++ tailWord_997618).sum := by decide
  have hdescent : baseEnd_997618 < baseStart_997618 := by decide
  rcases family_descends (prefixWord ++ tailWord_997618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997631 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 5]
def baseStart_997631 : Nat := 118140960795 + 997631 * 2 ^ 59
def prefixEnd_997631 : Nat := 4983230072969 + 3 ^ 40 * 997631 * 2
def baseEnd_997631 : Nat := 113836493072375888405441

theorem tailTrace_997631 : CollatzResearch.WordTrace tailWord_997631 prefixEnd_997631 113836493072375888405441 := by
  unfold tailWord_997631
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386591848760743655120747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24257727899173829103413831 36386591848760743655120747)
  ·
    refine ⟨54579887773141115482681121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36386591848760743655120747 54579887773141115482681121)
    ·
      refine ⟨40934915829855836612010841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54579887773141115482681121 40934915829855836612010841)
      ·
        refine ⟨30701186872391877459008131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40934915829855836612010841 30701186872391877459008131)
        ·
          refine ⟨46051780308587816188512197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30701186872391877459008131 46051780308587816188512197)
          ·
            refine ⟨8634708807860215535346037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46051780308587816188512197 8634708807860215535346037)
            ·
              refine ⟨809503950736895206438691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8634708807860215535346037 809503950736895206438691)
              ·
                refine ⟨1214255926105342809658037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809503950736895206438691 1214255926105342809658037)
                ·
                  refine ⟨113836493072375888405441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1214255926105342809658037 113836493072375888405441)
                  ·
                    rfl

theorem cell22_997631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 5].length) (baseStart_997631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997631 prefixEnd_997631 := by exact prefixLift 997631
  have htrace : WordTrace (prefixWord ++ tailWord_997631) baseStart_997631 baseEnd_997631 := by
    simpa [prefixWord, tailWord_997631, baseEnd_997631] using wordTrace_append hprefix tailTrace_997631
  have hstable : (prefixWord ++ tailWord_997631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997631).length < 2 ^ (prefixWord ++ tailWord_997631).sum := by decide
  have hdescent : baseEnd_997631 < baseStart_997631 := by decide
  rcases family_descends (prefixWord ++ tailWord_997631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997676 : List Nat := [2, 2, 1, 1, 1, 3, 2, 6, 4]
def baseStart_997676 : Nat := 118140960795 + 997676 * 2 ^ 59
def prefixEnd_997676 : Nat := 4983230072969 + 3 ^ 40 * 997676 * 2
def baseEnd_997676 : Nat := 113841627878920849280395

theorem tailTrace_997676 : CollatzResearch.WordTrace tailWord_997676 prefixEnd_997676 113841627878920849280395 := by
  unfold tailWord_997676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18194116566798858170254441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24258822089065144227005921 18194116566798858170254441)
  ·
    refine ⟨13645587425099143627690831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18194116566798858170254441 13645587425099143627690831)
    ·
      refine ⟨20468381137648715441536247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13645587425099143627690831 20468381137648715441536247)
      ·
        refine ⟨30702571706473073162304371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20468381137648715441536247 30702571706473073162304371)
        ·
          refine ⟨46053857559709609743456557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30702571706473073162304371 46053857559709609743456557)
          ·
            refine ⟨17270196584891103653796209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46053857559709609743456557 17270196584891103653796209)
            ·
              refine ⟨12952647438668327740347157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17270196584891103653796209 12952647438668327740347157)
              ·
                refine ⟨607155348687577862828773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12952647438668327740347157 607155348687577862828773)
                ·
                  refine ⟨113841627878920849280395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607155348687577862828773 113841627878920849280395)
                  ·
                    rfl

theorem cell22_997676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_997676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997676 prefixEnd_997676 := by exact prefixLift 997676
  have htrace : WordTrace (prefixWord ++ tailWord_997676) baseStart_997676 baseEnd_997676 := by
    simpa [prefixWord, tailWord_997676, baseEnd_997676] using wordTrace_append hprefix tailTrace_997676
  have hstable : (prefixWord ++ tailWord_997676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997676).length < 2 ^ (prefixWord ++ tailWord_997676).sum := by decide
  have hdescent : baseEnd_997676 < baseStart_997676 := by decide
  rcases family_descends (prefixWord ++ tailWord_997676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997704 : List Nat := [2, 1, 3, 1, 1, 2, 4, 8]
def baseStart_997704 : Nat := 118140960795 + 997704 * 2 ^ 59
def prefixEnd_997704 : Nat := 4983230072969 + 3 ^ 40 * 997704 * 2
def baseEnd_997704 : Nat := 37948274289886645349011

theorem tailTrace_997704 : CollatzResearch.WordTrace tailWord_997704 prefixEnd_997704 37948274289886645349011 := by
  unfold tailWord_997704
  simp only [CollatzResearch.WordTrace]
  refine ⟨18194627188748138561264083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24259502918330851415018777 18194627188748138561264083)
  ·
    refine ⟨27291940783122207841896125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18194627188748138561264083 27291940783122207841896125)
    ·
      refine ⟨10234477793670827940711047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27291940783122207841896125 10234477793670827940711047)
      ·
        refine ⟨15351716690506241911066571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10234477793670827940711047 15351716690506241911066571)
        ·
          refine ⟨23027575035759362866599857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15351716690506241911066571 23027575035759362866599857)
          ·
            refine ⟨17270681276819522149949893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23027575035759362866599857 17270681276819522149949893)
            ·
              refine ⟨3238252739403660403115605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17270681276819522149949893 3238252739403660403115605)
              ·
                refine ⟨37948274289886645349011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3238252739403660403115605 37948274289886645349011)
                ·
                  rfl

theorem cell22_997704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 8].length) (baseStart_997704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997704 prefixEnd_997704 := by exact prefixLift 997704
  have htrace : WordTrace (prefixWord ++ tailWord_997704) baseStart_997704 baseEnd_997704 := by
    simpa [prefixWord, tailWord_997704, baseEnd_997704] using wordTrace_append hprefix tailTrace_997704
  have hstable : (prefixWord ++ tailWord_997704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997704).length < 2 ^ (prefixWord ++ tailWord_997704).sum := by decide
  have hdescent : baseEnd_997704 < baseStart_997704 := by decide
  rcases family_descends (prefixWord ++ tailWord_997704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997738 : List Nat := [3, 1, 3, 3, 1, 3, 1, 7]
def baseStart_997738 : Nat := 118140960795 + 997738 * 2 ^ 59
def prefixEnd_997738 : Nat := 4983230072969 + 3 ^ 40 * 997738 * 2
def baseEnd_997738 : Nat := 37949567500423894754555

theorem tailTrace_997738 : CollatzResearch.WordTrace tailWord_997738 prefixEnd_997738 37949567500423894754555 := by
  unfold tailWord_997738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9097623614843275232316467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24260329639582067286177245 9097623614843275232316467)
  ·
    refine ⟨13646435422264912848474701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9097623614843275232316467 13646435422264912848474701)
    ·
      refine ⟨5117413283349342318178013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13646435422264912848474701 5117413283349342318178013)
      ·
        refine ⟨1919029981256003369316755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5117413283349342318178013 1919029981256003369316755)
        ·
          refine ⟨2878544971884005053975133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919029981256003369316755 2878544971884005053975133)
          ·
            refine ⟨1079454364456501895240675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2878544971884005053975133 1079454364456501895240675)
            ·
              refine ⟨1619181546684752842861013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079454364456501895240675 1619181546684752842861013)
              ·
                refine ⟨37949567500423894754555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1619181546684752842861013 37949567500423894754555)
                ·
                  rfl

theorem cell22_997738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_997738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997738 prefixEnd_997738 := by exact prefixLift 997738
  have htrace : WordTrace (prefixWord ++ tailWord_997738) baseStart_997738 baseEnd_997738 := by
    simpa [prefixWord, tailWord_997738, baseEnd_997738] using wordTrace_append hprefix tailTrace_997738
  have hstable : (prefixWord ++ tailWord_997738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997738).length < 2 ^ (prefixWord ++ tailWord_997738).sum := by decide
  have hdescent : baseEnd_997738 < baseStart_997738 := by decide
  rcases family_descends (prefixWord ++ tailWord_997738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997796 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_997796 : Nat := 118140960795 + 997796 * 2 ^ 59
def prefixEnd_997796 : Nat := 4983230072969 + 3 ^ 40 * 997796 * 2
def baseEnd_997796 : Nat := 341565962089122234840817

theorem tailTrace_997796 : CollatzResearch.WordTrace tailWord_997796 prefixEnd_997796 341565962089122234840817 := by
  unfold tailWord_997796
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196304946581488417438621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24261739928775317889918161 18196304946581488417438621)
  ·
    refine ⟨6823614354968058156539483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18196304946581488417438621 6823614354968058156539483)
    ·
      refine ⟨10235421532452087234809225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6823614354968058156539483 10235421532452087234809225)
      ·
        refine ⟨7676566149339065426106919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10235421532452087234809225 7676566149339065426106919)
        ·
          refine ⟨11514849224008598139160379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7676566149339065426106919 11514849224008598139160379)
          ·
            refine ⟨17272273836012897208740569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11514849224008598139160379 17272273836012897208740569)
            ·
              refine ⟨12954205377009672906555427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17272273836012897208740569 12954205377009672906555427)
              ·
                refine ⟨19431308065514509359833141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12954205377009672906555427 19431308065514509359833141)
                ·
                  refine ⟨1821685131141985252484357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19431308065514509359833141 1821685131141985252484357)
                  ·
                    refine ⟨341565962089122234840817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1821685131141985252484357 341565962089122234840817)
                    ·
                      rfl

theorem cell22_997796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_997796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997796 prefixEnd_997796 := by exact prefixLift 997796
  have htrace : WordTrace (prefixWord ++ tailWord_997796) baseStart_997796 baseEnd_997796 := by
    simpa [prefixWord, tailWord_997796, baseEnd_997796] using wordTrace_append hprefix tailTrace_997796
  have hstable : (prefixWord ++ tailWord_997796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997796).length < 2 ^ (prefixWord ++ tailWord_997796).sum := by decide
  have hdescent : baseEnd_997796 < baseStart_997796 := by decide
  rcases family_descends (prefixWord ++ tailWord_997796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997856 : List Nat := [2, 1, 1, 3, 1, 1, 6, 7]
def baseStart_997856 : Nat := 118140960795 + 997856 * 2 ^ 59
def prefixEnd_997856 : Nat := 4983230072969 + 3 ^ 40 * 997856 * 2
def baseEnd_997856 : Nat := 37954055701700230926737

theorem tailTrace_997856 : CollatzResearch.WordTrace tailWord_997856 prefixEnd_997856 37954055701700230926737 := by
  unfold tailWord_997856
  simp only [CollatzResearch.WordTrace]
  refine ⟨18197399136472803541030711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24263198848630404721374281 18197399136472803541030711)
  ·
    refine ⟨27296098704709205311546067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18197399136472803541030711 27296098704709205311546067)
    ·
      refine ⟨40944148057063807967319101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27296098704709205311546067 40944148057063807967319101)
      ·
        refine ⟨15354055521398927987744663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40944148057063807967319101 15354055521398927987744663)
        ·
          refine ⟨23031083282098391981616995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15354055521398927987744663 23031083282098391981616995)
          ·
            refine ⟨34546624923147587972425493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23031083282098391981616995 34546624923147587972425493)
            ·
              refine ⟨1619373043272543186207445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34546624923147587972425493 1619373043272543186207445)
              ·
                refine ⟨37954055701700230926737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1619373043272543186207445 37954055701700230926737)
                ·
                  rfl

theorem cell22_997856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 7].length) (baseStart_997856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997856 prefixEnd_997856 := by exact prefixLift 997856
  have htrace : WordTrace (prefixWord ++ tailWord_997856) baseStart_997856 baseEnd_997856 := by
    simpa [prefixWord, tailWord_997856, baseEnd_997856] using wordTrace_append hprefix tailTrace_997856
  have hstable : (prefixWord ++ tailWord_997856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997856).length < 2 ^ (prefixWord ++ tailWord_997856).sum := by decide
  have hdescent : baseEnd_997856 < baseStart_997856 := by decide
  rcases family_descends (prefixWord ++ tailWord_997856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997890 : List Nat := [3, 4, 1, 2, 3, 9]
def baseStart_997890 : Nat := 118140960795 + 997890 * 2 ^ 59
def prefixEnd_997890 : Nat := 4983230072969 + 3 ^ 40 * 997890 * 2
def baseEnd_997890 : Nat := 4217260990248608925809

theorem tailTrace_997890 : CollatzResearch.WordTrace tailWord_997890 prefixEnd_997890 4217260990248608925809 := by
  unfold tailWord_997890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099009588705607722199781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24264025569881620592532749 9099009588705607722199781)
  ·
    refine ⟨1706064297882301447912459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9099009588705607722199781 1706064297882301447912459)
    ·
      refine ⟨2559096446823452171868689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706064297882301447912459 2559096446823452171868689)
      ·
        refine ⟨1919322335117589128901517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2559096446823452171868689 1919322335117589128901517)
        ·
          refine ⟨719745875669095923338069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1919322335117589128901517 719745875669095923338069)
          ·
            refine ⟨4217260990248608925809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 719745875669095923338069 4217260990248608925809)
            ·
              rfl

theorem cell22_997890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 9].length) (baseStart_997890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997890 prefixEnd_997890 := by exact prefixLift 997890
  have htrace : WordTrace (prefixWord ++ tailWord_997890) baseStart_997890 baseEnd_997890 := by
    simpa [prefixWord, tailWord_997890, baseEnd_997890] using wordTrace_append hprefix tailTrace_997890
  have hstable : (prefixWord ++ tailWord_997890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997890).length < 2 ^ (prefixWord ++ tailWord_997890).sum := by decide
  have hdescent : baseEnd_997890 < baseStart_997890 := by decide
  rcases family_descends (prefixWord ++ tailWord_997890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997956 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_997956 : Nat := 118140960795 + 997956 * 2 ^ 59
def prefixEnd_997956 : Nat := 4983230072969 + 3 ^ 40 * 997956 * 2
def baseEnd_997956 : Nat := 341620733358935150840327

theorem tailTrace_997956 : CollatzResearch.WordTrace tailWord_997956 prefixEnd_997956 341620733358935150840327 := by
  unfold tailWord_997956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18199222786291662080350861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24265630381722216107134481 18199222786291662080350861)
  ·
    refine ⟨6824708544859373280131573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18199222786291662080350861 6824708544859373280131573)
    ·
      refine ⟨639816426080566245012335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6824708544859373280131573 639816426080566245012335)
      ·
        refine ⟨959724639120849367518503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639816426080566245012335 959724639120849367518503)
        ·
          refine ⟨1439586958681274051277755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959724639120849367518503 1439586958681274051277755)
          ·
            refine ⟨2159380438021911076916633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439586958681274051277755 2159380438021911076916633)
            ·
              refine ⟨1619535328516433307687475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2159380438021911076916633 1619535328516433307687475)
              ·
                refine ⟨2429302992774649961531213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619535328516433307687475 2429302992774649961531213)
                ·
                  refine ⟨910988622290493735574205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2429302992774649961531213 910988622290493735574205)
                  ·
                    refine ⟨341620733358935150840327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 910988622290493735574205 341620733358935150840327)
                    ·
                      rfl

theorem cell22_997956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_997956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997956 prefixEnd_997956 := by exact prefixLift 997956
  have htrace : WordTrace (prefixWord ++ tailWord_997956) baseStart_997956 baseEnd_997956 := by
    simpa [prefixWord, tailWord_997956, baseEnd_997956] using wordTrace_append hprefix tailTrace_997956
  have hstable : (prefixWord ++ tailWord_997956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997956).length < 2 ^ (prefixWord ++ tailWord_997956).sum := by decide
  have hdescent : baseEnd_997956 < baseStart_997956 := by decide
  rcases family_descends (prefixWord ++ tailWord_997956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997961 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_997961 : Nat := 118140960795 + 997961 * 2 ^ 59
def prefixEnd_997961 : Nat := 4983230072969 + 3 ^ 40 * 997961 * 2
def baseEnd_997961 : Nat := 341622444961116804465311

theorem tailTrace_997961 : CollatzResearch.WordTrace tailWord_997961 prefixEnd_997961 341622444961116804465311 := by
  unfold tailWord_997961
  simp only [CollatzResearch.WordTrace]
  refine ⟨36398627937565210014633737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24265751958376806676422491 36398627937565210014633737)
  ·
    refine ⟨27298970953173907510975303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36398627937565210014633737 27298970953173907510975303)
    ·
      refine ⟨40948456429760861266462955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27298970953173907510975303 40948456429760861266462955)
      ·
        refine ⟨61422684644641291899694433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40948456429760861266462955 61422684644641291899694433)
        ·
          refine ⟨46067013483480968924770825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61422684644641291899694433 46067013483480968924770825)
          ·
            refine ⟨34550260112610726693578119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46067013483480968924770825 34550260112610726693578119)
            ·
              refine ⟨51825390168916090040367179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34550260112610726693578119 51825390168916090040367179)
              ·
                refine ⟨77738085253374135060550769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51825390168916090040367179 77738085253374135060550769)
                ·
                  refine ⟨58303563940030601295413077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77738085253374135060550769 58303563940030601295413077)
                  ·
                    refine ⟨341622444961116804465311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 58303563940030601295413077 341622444961116804465311)
                    ·
                      rfl

theorem cell22_997961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_997961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997961 prefixEnd_997961 := by exact prefixLift 997961
  have htrace : WordTrace (prefixWord ++ tailWord_997961) baseStart_997961 baseEnd_997961 := by
    simpa [prefixWord, tailWord_997961, baseEnd_997961] using wordTrace_append hprefix tailTrace_997961
  have hstable : (prefixWord ++ tailWord_997961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997961).length < 2 ^ (prefixWord ++ tailWord_997961).sum := by decide
  have hdescent : baseEnd_997961 < baseStart_997961 := by decide
  rcases family_descends (prefixWord ++ tailWord_997961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997993 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_997993 : Nat := 118140960795 + 997993 * 2 ^ 59
def prefixEnd_997993 : Nat := 4983230072969 + 3 ^ 40 * 997993 * 2
def baseEnd_997993 : Nat := 341633399215079387665213

theorem tailTrace_997993 : CollatzResearch.WordTrace tailWord_997993 prefixEnd_997993 341633399215079387665213 := by
  unfold tailWord_997993
  simp only [CollatzResearch.WordTrace]
  refine ⟨36399795073449279479798633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24266530048966186319865755 36399795073449279479798633)
  ·
    refine ⟨27299846305086959609848975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36399795073449279479798633 27299846305086959609848975)
    ·
      refine ⟨40949769457630439414773463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27299846305086959609848975 40949769457630439414773463)
      ·
        refine ⟨61424654186445659122160195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40949769457630439414773463 61424654186445659122160195)
        ·
          refine ⟨92136981279668488683240293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61424654186445659122160195 92136981279668488683240293)
          ·
            refine ⟨17275683989937841628107555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92136981279668488683240293 17275683989937841628107555)
            ·
              refine ⟨25913525984906762442161333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17275683989937841628107555 25913525984906762442161333)
              ·
                refine ⟨2429393061085008978952625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25913525984906762442161333 2429393061085008978952625)
                ·
                  refine ⟨1822044795813756734214469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2429393061085008978952625 1822044795813756734214469)
                  ·
                    refine ⟨341633399215079387665213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1822044795813756734214469 341633399215079387665213)
                    ·
                      rfl

theorem cell22_997993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_997993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997993 prefixEnd_997993 := by exact prefixLift 997993
  have htrace : WordTrace (prefixWord ++ tailWord_997993) baseStart_997993 baseEnd_997993 := by
    simpa [prefixWord, tailWord_997993, baseEnd_997993] using wordTrace_append hprefix tailTrace_997993
  have hstable : (prefixWord ++ tailWord_997993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997993).length < 2 ^ (prefixWord ++ tailWord_997993).sum := by decide
  have hdescent : baseEnd_997993 < baseStart_997993 := by decide
  rcases family_descends (prefixWord ++ tailWord_997993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997997 : List Nat := [1, 5, 1, 1, 3, 1, 3, 3, 4]
def baseStart_997997 : Nat := 118140960795 + 997997 * 2 ^ 59
def prefixEnd_997997 : Nat := 4983230072969 + 3 ^ 40 * 997997 * 2
def baseEnd_997997 : Nat := 113878256165608236855067

theorem tailTrace_997997 : CollatzResearch.WordTrace tailWord_997997 prefixEnd_997997 113878256165608236855067 := by
  unfold tailWord_997997
  simp only [CollatzResearch.WordTrace]
  refine ⟨36399940965434788162944245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24266627310289858775296163 36399940965434788162944245)
  ·
    refine ⟨3412494465509511390276023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36399940965434788162944245 3412494465509511390276023)
    ·
      refine ⟨5118741698264267085414035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3412494465509511390276023 5118741698264267085414035)
      ·
        refine ⟨7678112547396400628121053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118741698264267085414035 7678112547396400628121053)
        ·
          refine ⟨2879292205273650235545395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7678112547396400628121053 2879292205273650235545395)
          ·
            refine ⟨4318938307910475353318093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879292205273650235545395 4318938307910475353318093)
            ·
              refine ⟨1619601865466428257494285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4318938307910475353318093 1619601865466428257494285)
              ·
                refine ⟨607350699549910596560357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1619601865466428257494285 607350699549910596560357)
                ·
                  refine ⟨113878256165608236855067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607350699549910596560357 113878256165608236855067)
                  ·
                    rfl

theorem cell22_997997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_997997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_997997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_997997 prefixEnd_997997 := by exact prefixLift 997997
  have htrace : WordTrace (prefixWord ++ tailWord_997997) baseStart_997997 baseEnd_997997 := by
    simpa [prefixWord, tailWord_997997, baseEnd_997997] using wordTrace_append hprefix tailTrace_997997
  have hstable : (prefixWord ++ tailWord_997997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997997).length < 2 ^ (prefixWord ++ tailWord_997997).sum := by decide
  have hdescent : baseEnd_997997 < baseStart_997997 := by decide
  rcases family_descends (prefixWord ++ tailWord_997997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998040 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 5, 3]
def baseStart_998040 : Nat := 118140960795 + 998040 * 2 ^ 59
def prefixEnd_998040 : Nat := 4983230072969 + 3 ^ 40 * 998040 * 2
def baseEnd_998040 : Nat := 341649488275586931740069

theorem tailTrace_998040 : CollatzResearch.WordTrace tailWord_998040 prefixEnd_998040 341649488275586931740069 := by
  unfold tailWord_998040
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200754652139503253379787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24267672869519337671173049 18200754652139503253379787)
  ·
    refine ⟨27301131978209254880069681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18200754652139503253379787 27301131978209254880069681)
    ·
      refine ⟨20475848983656941160052261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27301131978209254880069681 20475848983656941160052261)
      ·
        refine ⟨3839221684435676467509799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20475848983656941160052261 3839221684435676467509799)
        ·
          refine ⟨5758832526653514701264699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839221684435676467509799 5758832526653514701264699)
          ·
            refine ⟨8638248789980272051897049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758832526653514701264699 8638248789980272051897049)
            ·
              refine ⟨6478686592485204038922787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8638248789980272051897049 6478686592485204038922787)
              ·
                refine ⟨9718029888727806058384181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478686592485204038922787 9718029888727806058384181)
                ·
                  refine ⟨911065302068231817973517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9718029888727806058384181 911065302068231817973517)
                  ·
                    refine ⟨341649488275586931740069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 911065302068231817973517 341649488275586931740069)
                    ·
                      rfl

theorem cell22_998040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_998040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998040 prefixEnd_998040 := by exact prefixLift 998040
  have htrace : WordTrace (prefixWord ++ tailWord_998040) baseStart_998040 baseEnd_998040 := by
    simpa [prefixWord, tailWord_998040, baseEnd_998040] using wordTrace_append hprefix tailTrace_998040
  have hstable : (prefixWord ++ tailWord_998040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998040).length < 2 ^ (prefixWord ++ tailWord_998040).sum := by decide
  have hdescent : baseEnd_998040 < baseStart_998040 := by decide
  rcases family_descends (prefixWord ++ tailWord_998040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998117 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_998117 : Nat := 118140960795 + 998117 * 2 ^ 59
def prefixEnd_998117 : Nat := 4983230072969 + 3 ^ 40 * 998117 * 2
def baseEnd_998117 : Nat := 341675846949184397564833

theorem tailTrace_998117 : CollatzResearch.WordTrace tailWord_998117 prefixEnd_998117 341675846949184397564833 := by
  unfold tailWord_998117
  simp only [CollatzResearch.WordTrace]
  refine ⟨36404317725000048657312605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24269545150000032438208403 36404317725000048657312605)
  ·
    refine ⟨13651619146875018246492227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36404317725000048657312605 13651619146875018246492227)
    ·
      refine ⟨20477428720312527369738341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13651619146875018246492227 20477428720312527369738341)
      ·
        refine ⟨3839517885058598881825939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20477428720312527369738341 3839517885058598881825939)
        ·
          refine ⟨5759276827587898322738909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839517885058598881825939 5759276827587898322738909)
          ·
            refine ⟨2159728810345461871027091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5759276827587898322738909 2159728810345461871027091)
            ·
              refine ⟨3239593215518192806540637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159728810345461871027091 3239593215518192806540637)
              ·
                refine ⟨1214847455819322302452739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3239593215518192806540637 1214847455819322302452739)
                ·
                  refine ⟨1822271183728983453679109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214847455819322302452739 1822271183728983453679109)
                  ·
                    refine ⟨341675846949184397564833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1822271183728983453679109 341675846949184397564833)
                    ·
                      rfl

theorem cell22_998117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_998117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998117 prefixEnd_998117 := by exact prefixLift 998117
  have htrace : WordTrace (prefixWord ++ tailWord_998117) baseStart_998117 baseEnd_998117 := by
    simpa [prefixWord, tailWord_998117, baseEnd_998117] using wordTrace_append hprefix tailTrace_998117
  have hstable : (prefixWord ++ tailWord_998117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998117).length < 2 ^ (prefixWord ++ tailWord_998117).sum := by decide
  have hdescent : baseEnd_998117 < baseStart_998117 := by decide
  rcases family_descends (prefixWord ++ tailWord_998117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998143 : List Nat := [1, 1, 2, 2, 1, 3, 1, 11]
def baseStart_998143 : Nat := 118140960795 + 998143 * 2 ^ 59
def prefixEnd_998143 : Nat := 4983230072969 + 3 ^ 40 * 998143 * 2
def baseEnd_998143 : Nat := 37964971920058777379417

theorem tailTrace_998143 : CollatzResearch.WordTrace tailWord_998143 prefixEnd_998143 37964971920058777379417 := by
  unfold tailWord_998143
  simp only [CollatzResearch.WordTrace]
  refine ⟨36405266022905855097759083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24270177348603903398506055 36405266022905855097759083)
  ·
    refine ⟨54607899034358782646638625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36405266022905855097759083 54607899034358782646638625)
    ·
      refine ⟨40955924275769086984978969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54607899034358782646638625 40955924275769086984978969)
      ·
        refine ⟨30716943206826815238734227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40955924275769086984978969 30716943206826815238734227)
        ·
          refine ⟨46075414810240222858101341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30716943206826815238734227 46075414810240222858101341)
          ·
            refine ⟨17278280553840083571788003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46075414810240222858101341 17278280553840083571788003)
            ·
              refine ⟨25917420830760125357682005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17278280553840083571788003 25917420830760125357682005)
              ·
                refine ⟨37964971920058777379417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 25917420830760125357682005 37964971920058777379417)
                ·
                  rfl

theorem cell22_998143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 11].length) (baseStart_998143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998143 prefixEnd_998143 := by exact prefixLift 998143
  have htrace : WordTrace (prefixWord ++ tailWord_998143) baseStart_998143 baseEnd_998143 := by
    simpa [prefixWord, tailWord_998143, baseEnd_998143] using wordTrace_append hprefix tailTrace_998143
  have hstable : (prefixWord ++ tailWord_998143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998143).length < 2 ^ (prefixWord ++ tailWord_998143).sum := by decide
  have hdescent : baseEnd_998143 < baseStart_998143 := by decide
  rcases family_descends (prefixWord ++ tailWord_998143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998243 : List Nat := [1, 1, 1, 5, 3, 3, 2, 2, 1, 3]
def baseStart_998243 : Nat := 118140960795 + 998243 * 2 ^ 59
def prefixEnd_998243 : Nat := 4983230072969 + 3 ^ 40 * 998243 * 2
def baseEnd_998243 : Nat := 341718979324162068914447

theorem tailTrace_998243 : CollatzResearch.WordTrace tailWord_998243 prefixEnd_998243 341718979324162068914447 := by
  unfold tailWord_998243
  simp only [CollatzResearch.WordTrace]
  refine ⟨36408913322543572176399383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24272608881695714784266255 36408913322543572176399383)
  ·
    refine ⟨54613369983815358264599075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36408913322543572176399383 54613369983815358264599075)
    ·
      refine ⟨81920054975723037396898613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54613369983815358264599075 81920054975723037396898613)
      ·
        refine ⟨7680005153974034755959245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81920054975723037396898613 7680005153974034755959245)
        ·
          refine ⟨2880001932740263033484717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7680005153974034755959245 2880001932740263033484717)
          ·
            refine ⟨1080000724777598637556769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2880001932740263033484717 1080000724777598637556769)
            ·
              refine ⟨810000543583198978167577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080000724777598637556769 810000543583198978167577)
              ·
                refine ⟨607500407687399233625683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810000543583198978167577 607500407687399233625683)
                ·
                  refine ⟨911250611531098850438525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 607500407687399233625683 911250611531098850438525)
                  ·
                    refine ⟨341718979324162068914447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 911250611531098850438525 341718979324162068914447)
                    ·
                      rfl

theorem cell22_998243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 3].length) (baseStart_998243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998243 prefixEnd_998243 := by exact prefixLift 998243
  have htrace : WordTrace (prefixWord ++ tailWord_998243) baseStart_998243 baseEnd_998243 := by
    simpa [prefixWord, tailWord_998243, baseEnd_998243] using wordTrace_append hprefix tailTrace_998243
  have hstable : (prefixWord ++ tailWord_998243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998243).length < 2 ^ (prefixWord ++ tailWord_998243).sum := by decide
  have hdescent : baseEnd_998243 < baseStart_998243 := by decide
  rcases family_descends (prefixWord ++ tailWord_998243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998254 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_998254 : Nat := 118140960795 + 998254 * 2 ^ 59
def prefixEnd_998254 : Nat := 4983230072969 + 3 ^ 40 * 998254 * 2
def baseEnd_998254 : Nat := 341722744848961706889413

theorem tailTrace_998254 : CollatzResearch.WordTrace tailWord_998254 prefixEnd_998254 341722744848961706889413 := by
  unfold tailWord_998254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551164315687965131881227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24272876350335814036699877 4551164315687965131881227)
  ·
    refine ⟨6826746473531947697821841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4551164315687965131881227 6826746473531947697821841)
    ·
      refine ⟨5120059855148960773366381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6826746473531947697821841 5120059855148960773366381)
      ·
        refine ⟨1920022445680860290012393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5120059855148960773366381 1920022445680860290012393)
        ·
          refine ⟨1440016834260645217509295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1920022445680860290012393 1440016834260645217509295)
          ·
            refine ⟨2160025251390967826263943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440016834260645217509295 2160025251390967826263943)
            ·
              refine ⟨3240037877086451739395915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160025251390967826263943 3240037877086451739395915)
              ·
                refine ⟨4860056815629677609093873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240037877086451739395915 4860056815629677609093873)
                ·
                  refine ⟨3645042611722258206820405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4860056815629677609093873 3645042611722258206820405)
                  ·
                    refine ⟨341722744848961706889413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3645042611722258206820405 341722744848961706889413)
                    ·
                      rfl

theorem cell22_998254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_998254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998254 prefixEnd_998254 := by exact prefixLift 998254
  have htrace : WordTrace (prefixWord ++ tailWord_998254) baseStart_998254 baseEnd_998254 := by
    simpa [prefixWord, tailWord_998254, baseEnd_998254] using wordTrace_append hprefix tailTrace_998254
  have hstable : (prefixWord ++ tailWord_998254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998254).length < 2 ^ (prefixWord ++ tailWord_998254).sum := by decide
  have hdescent : baseEnd_998254 < baseStart_998254 := by decide
  rcases family_descends (prefixWord ++ tailWord_998254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998295 : List Nat := [1, 1, 3, 3, 1, 2, 11]
def baseStart_998295 : Nat := 118140960795 + 998295 * 2 ^ 59
def prefixEnd_998295 : Nat := 4983230072969 + 3 ^ 40 * 998295 * 2
def baseEnd_998295 : Nat := 12656917777290787652381

theorem tailTrace_998295 : CollatzResearch.WordTrace tailWord_998295 prefixEnd_998295 12656917777290787652381 := by
  unfold tailWord_998295
  simp only [CollatzResearch.WordTrace]
  refine ⟨36410809918355185057292339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24273873278903456704861559 36410809918355185057292339)
  ·
    refine ⟨54616214877532777585938509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36410809918355185057292339 54616214877532777585938509)
    ·
      refine ⟨20481080579074791594726941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54616214877532777585938509 20481080579074791594726941)
      ·
        refine ⟨7680405217153046848022603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20481080579074791594726941 7680405217153046848022603)
        ·
          refine ⟨11520607825729570272033905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680405217153046848022603 11520607825729570272033905)
          ·
            refine ⟨8640455869297177704025429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11520607825729570272033905 8640455869297177704025429)
            ·
              refine ⟨12656917777290787652381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8640455869297177704025429 12656917777290787652381)
              ·
                rfl

theorem cell22_998295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 11].length) (baseStart_998295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998295 prefixEnd_998295 := by exact prefixLift 998295
  have htrace : WordTrace (prefixWord ++ tailWord_998295) baseStart_998295 baseEnd_998295 := by
    simpa [prefixWord, tailWord_998295, baseEnd_998295] using wordTrace_append hprefix tailTrace_998295
  have hstable : (prefixWord ++ tailWord_998295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998295).length < 2 ^ (prefixWord ++ tailWord_998295).sum := by decide
  have hdescent : baseEnd_998295 < baseStart_998295 := by decide
  rcases family_descends (prefixWord ++ tailWord_998295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998329 : List Nat := [1, 2, 1, 4, 2, 4, 2, 6]
def baseStart_998329 : Nat := 118140960795 + 998329 * 2 ^ 59
def prefixEnd_998329 : Nat := 4983230072969 + 3 ^ 40 * 998329 * 2
def baseEnd_998329 : Nat := 37972046542409612362687

theorem tailTrace_998329 : CollatzResearch.WordTrace tailWord_998329 prefixEnd_998329 37972046542409612362687 := by
  unfold tailWord_998329
  simp only [CollatzResearch.WordTrace]
  refine ⟨36412050000232008864030041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24274700000154672576020027 36412050000232008864030041)
  ·
    refine ⟨27309037500174006648022531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36412050000232008864030041 27309037500174006648022531)
    ·
      refine ⟨40963556250261009972033797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27309037500174006648022531 40963556250261009972033797)
      ·
        refine ⟨7680666796923939369756337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40963556250261009972033797 7680666796923939369756337)
        ·
          refine ⟨5760500097692954527317253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7680666796923939369756337 5760500097692954527317253)
          ·
            refine ⟨1080093768317428973871985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5760500097692954527317253 1080093768317428973871985)
            ·
              refine ⟨810070326238071730403989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080093768317428973871985 810070326238071730403989)
              ·
                refine ⟨37972046542409612362687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 810070326238071730403989 37972046542409612362687)
                ·
                  rfl

theorem cell22_998329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 6].length) (baseStart_998329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998329 prefixEnd_998329 := by exact prefixLift 998329
  have htrace : WordTrace (prefixWord ++ tailWord_998329) baseStart_998329 baseEnd_998329 := by
    simpa [prefixWord, tailWord_998329, baseEnd_998329] using wordTrace_append hprefix tailTrace_998329
  have hstable : (prefixWord ++ tailWord_998329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998329).length < 2 ^ (prefixWord ++ tailWord_998329).sum := by decide
  have hdescent : baseEnd_998329 < baseStart_998329 := by decide
  rcases family_descends (prefixWord ++ tailWord_998329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998361 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 3, 3]
def baseStart_998361 : Nat := 118140960795 + 998361 * 2 ^ 59
def prefixEnd_998361 : Nat := 4983230072969 + 3 ^ 40 * 998361 * 2
def baseEnd_998361 : Nat := 341759373135649094464085

theorem tailTrace_998361 : CollatzResearch.WordTrace tailWord_998361 prefixEnd_998361 341759373135649094464085 := by
  unfold tailWord_998361
  simp only [CollatzResearch.WordTrace]
  refine ⟨36413217136116078329194937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24275478090744052219463291 36413217136116078329194937)
  ·
    refine ⟨27309912852087058746896203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36413217136116078329194937 27309912852087058746896203)
    ·
      refine ⟨40964869278130588120344305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27309912852087058746896203 40964869278130588120344305)
      ·
        refine ⟨30723651958597941090258229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40964869278130588120344305 30723651958597941090258229)
        ·
          refine ⟨2880342371118556977211709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30723651958597941090258229 2880342371118556977211709)
          ·
            refine ⟨1080128389169458866454391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2880342371118556977211709 1080128389169458866454391)
            ·
              refine ⟨1620192583754188299681587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080128389169458866454391 1620192583754188299681587)
              ·
                refine ⟨2430288875631282449522381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620192583754188299681587 2430288875631282449522381)
                ·
                  refine ⟨911358328361730918570893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2430288875631282449522381 911358328361730918570893)
                  ·
                    refine ⟨341759373135649094464085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 911358328361730918570893 341759373135649094464085)
                    ·
                      rfl

theorem cell22_998361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_998361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998361 prefixEnd_998361 := by exact prefixLift 998361
  have htrace : WordTrace (prefixWord ++ tailWord_998361) baseStart_998361 baseEnd_998361 := by
    simpa [prefixWord, tailWord_998361, baseEnd_998361] using wordTrace_append hprefix tailTrace_998361
  have hstable : (prefixWord ++ tailWord_998361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998361).length < 2 ^ (prefixWord ++ tailWord_998361).sum := by decide
  have hdescent : baseEnd_998361 < baseStart_998361 := by decide
  rcases family_descends (prefixWord ++ tailWord_998361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998434 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_998434 : Nat := 118140960795 + 998434 * 2 ^ 59
def prefixEnd_998434 : Nat := 4983230072969 + 3 ^ 40 * 998434 * 2
def baseEnd_998434 : Nat := 341784362527501237388861

theorem tailTrace_998434 : CollatzResearch.WordTrace tailWord_998434 prefixEnd_998434 341784362527501237388861 := by
  unfold tailWord_998434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9103969916212902949150589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24277253109901074531068237 9103969916212902949150589)
  ·
    refine ⟨3413988718579838605931471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9103969916212902949150589 3413988718579838605931471)
    ·
      refine ⟨5120983077869757908897207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3413988718579838605931471 5120983077869757908897207)
      ·
        refine ⟨7681474616804636863345811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120983077869757908897207 7681474616804636863345811)
        ·
          refine ⟨11522211925206955295018717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7681474616804636863345811 11522211925206955295018717)
          ·
            refine ⟨4320829471952608235632019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11522211925206955295018717 4320829471952608235632019)
            ·
              refine ⟨6481244207928912353448029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320829471952608235632019 6481244207928912353448029)
              ·
                refine ⟨2430466577973342132543011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6481244207928912353448029 2430466577973342132543011)
                ·
                  refine ⟨3645699866960013198814517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430466577973342132543011 3645699866960013198814517)
                  ·
                    refine ⟨341784362527501237388861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3645699866960013198814517 341784362527501237388861)
                    ·
                      rfl

theorem cell22_998434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_998434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998434 prefixEnd_998434 := by exact prefixLift 998434
  have htrace : WordTrace (prefixWord ++ tailWord_998434) baseStart_998434 baseEnd_998434 := by
    simpa [prefixWord, tailWord_998434, baseEnd_998434] using wordTrace_append hprefix tailTrace_998434
  have hstable : (prefixWord ++ tailWord_998434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998434).length < 2 ^ (prefixWord ++ tailWord_998434).sum := by decide
  have hdescent : baseEnd_998434 < baseStart_998434 := by decide
  rcases family_descends (prefixWord ++ tailWord_998434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998498 : List Nat := [3, 3, 2, 2, 1, 3, 2, 6]
def baseStart_998498 : Nat := 118140960795 + 998498 * 2 ^ 59
def prefixEnd_998498 : Nat := 4983230072969 + 3 ^ 40 * 998498 * 2
def baseEnd_998498 : Nat := 37978474559491822643185

theorem tailTrace_998498 : CollatzResearch.WordTrace tailWord_998498 prefixEnd_998498 37978474559491822643185 := by
  unfold tailWord_998498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9104553484154937681733037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24278809291079833817954765 9104553484154937681733037)
  ·
    refine ⟨3414207556558101630649889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9104553484154937681733037 3414207556558101630649889)
    ·
      refine ⟨2560655667418576222987417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3414207556558101630649889 2560655667418576222987417)
      ·
        refine ⟨1920491750563932167240563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2560655667418576222987417 1920491750563932167240563)
        ·
          refine ⟨2880737625845898250860845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920491750563932167240563 2880737625845898250860845)
          ·
            refine ⟨1080276609692211844072817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2880737625845898250860845 1080276609692211844072817)
            ·
              refine ⟨810207457269158883054613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080276609692211844072817 810207457269158883054613)
              ·
                refine ⟨37978474559491822643185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 810207457269158883054613 37978474559491822643185)
                ·
                  rfl

theorem cell22_998498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_998498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998498 prefixEnd_998498 := by exact prefixLift 998498
  have htrace : WordTrace (prefixWord ++ tailWord_998498) baseStart_998498 baseEnd_998498 := by
    simpa [prefixWord, tailWord_998498, baseEnd_998498] using wordTrace_append hprefix tailTrace_998498
  have hstable : (prefixWord ++ tailWord_998498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998498).length < 2 ^ (prefixWord ++ tailWord_998498).sum := by decide
  have hdescent : baseEnd_998498 < baseStart_998498 := by decide
  rcases family_descends (prefixWord ++ tailWord_998498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998509 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 7]
def baseStart_998509 : Nat := 118140960795 + 998509 * 2 ^ 59
def prefixEnd_998509 : Nat := 4983230072969 + 3 ^ 40 * 998509 * 2
def baseEnd_998509 : Nat := 113936678853408680587877

theorem tailTrace_998509 : CollatzResearch.WordTrace tailWord_998509 prefixEnd_998509 113936678853408680587877 := by
  unfold tailWord_998509
  simp only [CollatzResearch.WordTrace]
  refine ⟨36418615139579899605582581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24279076759719933070388387 36418615139579899605582581)
  ·
    refine ⟨3414245169335615588023367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36418615139579899605582581 3414245169335615588023367)
    ·
      refine ⟨5121367754003423382035051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414245169335615588023367 5121367754003423382035051)
      ·
        refine ⟨7682051631005135073052577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121367754003423382035051 7682051631005135073052577)
        ·
          refine ⟨5761538723253851304789433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7682051631005135073052577 5761538723253851304789433)
          ·
            refine ⟨4321154042440388478592075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5761538723253851304789433 4321154042440388478592075)
            ·
              refine ⟨6481731063660582717888113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321154042440388478592075 6481731063660582717888113)
              ·
                refine ⟨4861298297745437038416085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6481731063660582717888113 4861298297745437038416085)
                ·
                  refine ⟨113936678853408680587877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4861298297745437038416085 113936678853408680587877)
                  ·
                    rfl

theorem cell22_998509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_998509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998509 prefixEnd_998509 := by exact prefixLift 998509
  have htrace : WordTrace (prefixWord ++ tailWord_998509) baseStart_998509 baseEnd_998509 := by
    simpa [prefixWord, tailWord_998509, baseEnd_998509] using wordTrace_append hprefix tailTrace_998509
  have hstable : (prefixWord ++ tailWord_998509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998509).length < 2 ^ (prefixWord ++ tailWord_998509).sum := by decide
  have hdescent : baseEnd_998509 < baseStart_998509 := by decide
  rcases family_descends (prefixWord ++ tailWord_998509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998556 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_998556 : Nat := 118140960795 + 998556 * 2 ^ 59
def prefixEnd_998556 : Nat := 4983230072969 + 3 ^ 40 * 998556 * 2
def baseEnd_998556 : Nat := 341826125620733585838487

theorem tailTrace_998556 : CollatzResearch.WordTrace tailWord_998556 prefixEnd_998556 341826125620733585838487 := by
  unfold tailWord_998556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18210164685204813316271761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24280219580273084421695681 18210164685204813316271761)
  ·
    refine ⟨13657623513903609987203821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18210164685204813316271761 13657623513903609987203821)
    ·
      refine ⟨5121608817713853745201433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13657623513903609987203821 5121608817713853745201433)
      ·
        refine ⟨3841206613285390308901075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121608817713853745201433 3841206613285390308901075)
        ·
          refine ⟨5761809919928085463351613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841206613285390308901075 5761809919928085463351613)
          ·
            refine ⟨2160678719973032048756855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5761809919928085463351613 2160678719973032048756855)
            ·
              refine ⟨3241018079959548073135283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160678719973032048756855 3241018079959548073135283)
              ·
                refine ⟨4861527119939322109702925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241018079959548073135283 4861527119939322109702925)
                ·
                  refine ⟨1823072669977245791138597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4861527119939322109702925 1823072669977245791138597)
                  ·
                    refine ⟨341826125620733585838487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823072669977245791138597 341826125620733585838487)
                    ·
                      rfl

theorem cell22_998556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_998556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998556 prefixEnd_998556 := by exact prefixLift 998556
  have htrace : WordTrace (prefixWord ++ tailWord_998556) baseStart_998556 baseEnd_998556 := by
    simpa [prefixWord, tailWord_998556, baseEnd_998556] using wordTrace_append hprefix tailTrace_998556
  have hstable : (prefixWord ++ tailWord_998556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998556).length < 2 ^ (prefixWord ++ tailWord_998556).sum := by decide
  have hdescent : baseEnd_998556 < baseStart_998556 := by decide
  rcases family_descends (prefixWord ++ tailWord_998556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998584 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_998584 : Nat := 118140960795 + 998584 * 2 ^ 59
def prefixEnd_998584 : Nat := 4983230072969 + 3 ^ 40 * 998584 * 2
def baseEnd_998584 : Nat := 341835710592950846138401

theorem tailTrace_998584 : CollatzResearch.WordTrace tailWord_998584 prefixEnd_998584 341835710592950846138401 := by
  unfold tailWord_998584
  simp only [CollatzResearch.WordTrace]
  refine ⟨18210675307154093707281403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24280900409538791609708537 18210675307154093707281403)
  ·
    refine ⟨27316012960731140560922105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18210675307154093707281403 27316012960731140560922105)
    ·
      refine ⟨20487009720548355420691579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27316012960731140560922105 20487009720548355420691579)
      ·
        refine ⟨30730514580822533131037369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20487009720548355420691579 30730514580822533131037369)
        ·
          refine ⟨23047885935616899848278027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30730514580822533131037369 23047885935616899848278027)
          ·
            refine ⟨34571828903425349772417041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23047885935616899848278027 34571828903425349772417041)
            ·
              refine ⟨25928871677569012329312781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34571828903425349772417041 25928871677569012329312781)
              ·
                refine ⟨9723326879088379623492293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25928871677569012329312781 9723326879088379623492293)
                ·
                  refine ⟨1823123789829071179404805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9723326879088379623492293 1823123789829071179404805)
                  ·
                    refine ⟨341835710592950846138401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823123789829071179404805 341835710592950846138401)
                    ·
                      rfl

theorem cell22_998584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_998584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998584 prefixEnd_998584 := by exact prefixLift 998584
  have htrace : WordTrace (prefixWord ++ tailWord_998584) baseStart_998584 baseEnd_998584 := by
    simpa [prefixWord, tailWord_998584, baseEnd_998584] using wordTrace_append hprefix tailTrace_998584
  have hstable : (prefixWord ++ tailWord_998584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998584).length < 2 ^ (prefixWord ++ tailWord_998584).sum := by decide
  have hdescent : baseEnd_998584 < baseStart_998584 := by decide
  rcases family_descends (prefixWord ++ tailWord_998584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998588 : List Nat := [2, 2, 2, 3, 2, 2, 1, 4, 4]
def baseStart_998588 : Nat := 118140960795 + 998588 * 2 ^ 59
def prefixEnd_998588 : Nat := 4983230072969 + 3 ^ 40 * 998588 * 2
def baseEnd_998588 : Nat := 113945693291565389679463

theorem tailTrace_998588 : CollatzResearch.WordTrace tailWord_998588 prefixEnd_998588 113945693291565389679463 := by
  unfold tailWord_998588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18210748253146848048854209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24280997670862464065138945 18210748253146848048854209)
  ·
    refine ⟨13658061189860136036640657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18210748253146848048854209 13658061189860136036640657)
    ·
      refine ⟨10243545892395102027480493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13658061189860136036640657 10243545892395102027480493)
      ·
        refine ⟨3841329709648163260305185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10243545892395102027480493 3841329709648163260305185)
        ·
          refine ⟨2880997282236122445228889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3841329709648163260305185 2880997282236122445228889)
          ·
            refine ⟨2160747961677091833921667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880997282236122445228889 2160747961677091833921667)
            ·
              refine ⟨3241121942515637750882501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160747961677091833921667 3241121942515637750882501)
              ·
                refine ⟨607710364221682078290469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3241121942515637750882501 607710364221682078290469)
                ·
                  refine ⟨113945693291565389679463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607710364221682078290469 113945693291565389679463)
                  ·
                    rfl

theorem cell22_998588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_998588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998588 prefixEnd_998588 := by exact prefixLift 998588
  have htrace : WordTrace (prefixWord ++ tailWord_998588) baseStart_998588 baseEnd_998588 := by
    simpa [prefixWord, tailWord_998588, baseEnd_998588] using wordTrace_append hprefix tailTrace_998588
  have hstable : (prefixWord ++ tailWord_998588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998588).length < 2 ^ (prefixWord ++ tailWord_998588).sum := by decide
  have hdescent : baseEnd_998588 < baseStart_998588 := by decide
  rcases family_descends (prefixWord ++ tailWord_998588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998605 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 6]
def baseStart_998605 : Nat := 118140960795 + 998605 * 2 ^ 59
def prefixEnd_998605 : Nat := 4983230072969 + 3 ^ 40 * 998605 * 2
def baseEnd_998605 : Nat := 113947633107371263787779

theorem tailTrace_998605 : CollatzResearch.WordTrace tailWord_998605 prefixEnd_998605 113947633107371263787779 := by
  unfold tailWord_998605
  simp only [CollatzResearch.WordTrace]
  refine ⟨36422116547232108001077269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24281411031488072000718179 36422116547232108001077269)
  ·
    refine ⟨1707286713151505062550497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36422116547232108001077269 1707286713151505062550497)
    ·
      refine ⟨1280465034863628796912873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1707286713151505062550497 1280465034863628796912873)
      ·
        refine ⟨960348776147721597684655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1280465034863628796912873 960348776147721597684655)
        ·
          refine ⟨1440523164221582396526983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960348776147721597684655 1440523164221582396526983)
          ·
            refine ⟨2160784746332373594790475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440523164221582396526983 2160784746332373594790475)
            ·
              refine ⟨3241177119498560392185713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160784746332373594790475 3241177119498560392185713)
              ·
                refine ⟨2430882839623920294139285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3241177119498560392185713 2430882839623920294139285)
                ·
                  refine ⟨113947633107371263787779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2430882839623920294139285 113947633107371263787779)
                  ·
                    rfl

theorem cell22_998605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_998605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998605 prefixEnd_998605 := by exact prefixLift 998605
  have htrace : WordTrace (prefixWord ++ tailWord_998605) baseStart_998605 baseEnd_998605 := by
    simpa [prefixWord, tailWord_998605, baseEnd_998605] using wordTrace_append hprefix tailTrace_998605
  have hstable : (prefixWord ++ tailWord_998605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998605).length < 2 ^ (prefixWord ++ tailWord_998605).sum := by decide
  have hdescent : baseEnd_998605 < baseStart_998605 := by decide
  rcases family_descends (prefixWord ++ tailWord_998605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998682 : List Nat := [3, 1, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_998682 : Nat := 118140960795 + 998682 * 2 ^ 59
def prefixEnd_998682 : Nat := 4983230072969 + 3 ^ 40 * 998682 * 2
def baseEnd_998682 : Nat := 341869257995711257188101

theorem tailTrace_998682 : CollatzResearch.WordTrace tailWord_998682 prefixEnd_998682 341869257995711257188101 := by
  unfold tailWord_998682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9106231241988287537907575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24283283311968766767753533 9106231241988287537907575)
  ·
    refine ⟨13659346862982431306861363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9106231241988287537907575 13659346862982431306861363)
    ·
      refine ⟨20489020294473646960292045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13659346862982431306861363 20489020294473646960292045)
      ·
        refine ⟨7683382610427617610109517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20489020294473646960292045 7683382610427617610109517)
        ·
          refine ⟨2881268478910356603791069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7683382610427617610109517 2881268478910356603791069)
          ·
            refine ⟨1080475679591383726421651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2881268478910356603791069 1080475679591383726421651)
            ·
              refine ⟨1620713519387075589632477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080475679591383726421651 1620713519387075589632477)
              ·
                refine ⟨607767569770153346112179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1620713519387075589632477 607767569770153346112179)
                ·
                  refine ⟨911651354655230019168269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 607767569770153346112179 911651354655230019168269)
                  ·
                    refine ⟨341869257995711257188101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 911651354655230019168269 341869257995711257188101)
                    ·
                      rfl

theorem cell22_998682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_998682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998682 prefixEnd_998682 := by exact prefixLift 998682
  have htrace : WordTrace (prefixWord ++ tailWord_998682) baseStart_998682 baseEnd_998682 := by
    simpa [prefixWord, tailWord_998682, baseEnd_998682] using wordTrace_append hprefix tailTrace_998682
  have hstable : (prefixWord ++ tailWord_998682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998682).length < 2 ^ (prefixWord ++ tailWord_998682).sum := by decide
  have hdescent : baseEnd_998682 < baseStart_998682 := by decide
  rcases family_descends (prefixWord ++ tailWord_998682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998708 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_998708 : Nat := 118140960795 + 998708 * 2 ^ 59
def prefixEnd_998708 : Nat := 4983230072969 + 3 ^ 40 * 998708 * 2
def baseEnd_998708 : Nat := 341878158327055856038021

theorem tailTrace_998708 : CollatzResearch.WordTrace tailWord_998708 prefixEnd_998708 341878158327055856038021 := by
  unfold tailWord_998708
  simp only [CollatzResearch.WordTrace]
  refine ⟨18212936632929478296038389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24283915510572637728051185 18212936632929478296038389)
  ·
    refine ⟨1707462809337138590253599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18212936632929478296038389 1707462809337138590253599)
    ·
      refine ⟨2561194214005707885380399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707462809337138590253599 2561194214005707885380399)
      ·
        refine ⟨3841791321008561828070599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561194214005707885380399 3841791321008561828070599)
        ·
          refine ⟨5762686981512842742105899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841791321008561828070599 5762686981512842742105899)
          ·
            refine ⟨8644030472269264113158849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5762686981512842742105899 8644030472269264113158849)
            ·
              refine ⟨6483022854201948084869137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8644030472269264113158849 6483022854201948084869137)
              ·
                refine ⟨4862267140651461063651853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483022854201948084869137 4862267140651461063651853)
                ·
                  refine ⟨1823350177744297898869445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4862267140651461063651853 1823350177744297898869445)
                  ·
                    refine ⟨341878158327055856038021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823350177744297898869445 341878158327055856038021)
                    ·
                      rfl

theorem cell22_998708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_998708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998708 prefixEnd_998708 := by exact prefixLift 998708
  have htrace : WordTrace (prefixWord ++ tailWord_998708) baseStart_998708 baseEnd_998708 := by
    simpa [prefixWord, tailWord_998708, baseEnd_998708] using wordTrace_append hprefix tailTrace_998708
  have hstable : (prefixWord ++ tailWord_998708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998708).length < 2 ^ (prefixWord ++ tailWord_998708).sum := by decide
  have hdescent : baseEnd_998708 < baseStart_998708 := by decide
  rcases family_descends (prefixWord ++ tailWord_998708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998755 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 2, 3]
def baseStart_998755 : Nat := 118140960795 + 998755 * 2 ^ 59
def prefixEnd_998755 : Nat := 4983230072969 + 3 ^ 40 * 998755 * 2
def baseEnd_998755 : Nat := 341894247387563400112877

theorem tailTrace_998755 : CollatzResearch.WordTrace tailWord_998755 prefixEnd_998755 341894247387563400112877 := by
  unfold tailWord_998755
  simp only [CollatzResearch.WordTrace]
  refine ⟨36427587496688683619037719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24285058331125789079358479 36427587496688683619037719)
  ·
    refine ⟨54641381245033025428556579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36427587496688683619037719 54641381245033025428556579)
    ·
      refine ⟨81962071867549538142834869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54641381245033025428556579 81962071867549538142834869)
      ·
        refine ⟨7683944237582769200890769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81962071867549538142834869 7683944237582769200890769)
        ·
          refine ⟨5762958178187076900668077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7683944237582769200890769 5762958178187076900668077)
          ·
            refine ⟨2161109316820153837750529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5762958178187076900668077 2161109316820153837750529)
            ·
              refine ⟨1620831987615115378312897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161109316820153837750529 1620831987615115378312897)
              ·
                refine ⟨1215623990711336533734673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620831987615115378312897 1215623990711336533734673)
                ·
                  refine ⟨911717993033502400301005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1215623990711336533734673 911717993033502400301005)
                  ·
                    refine ⟨341894247387563400112877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 911717993033502400301005 341894247387563400112877)
                    ·
                      rfl

theorem cell22_998755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 3].length) (baseStart_998755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998755 prefixEnd_998755 := by exact prefixLift 998755
  have htrace : WordTrace (prefixWord ++ tailWord_998755) baseStart_998755 baseEnd_998755 := by
    simpa [prefixWord, tailWord_998755, baseEnd_998755] using wordTrace_append hprefix tailTrace_998755
  have hstable : (prefixWord ++ tailWord_998755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998755).length < 2 ^ (prefixWord ++ tailWord_998755).sum := by decide
  have hdescent : baseEnd_998755 < baseStart_998755 := by decide
  rcases family_descends (prefixWord ++ tailWord_998755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998781 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_998781 : Nat := 118140960795 + 998781 * 2 ^ 59
def prefixEnd_998781 : Nat := 4983230072969 + 3 ^ 40 * 998781 * 2
def baseEnd_998781 : Nat := 341903147718907998962797

theorem tailTrace_998781 : CollatzResearch.WordTrace tailWord_998781 prefixEnd_998781 341903147718907998962797 := by
  unfold tailWord_998781
  simp only [CollatzResearch.WordTrace]
  refine ⟨36428535794594490059484197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24285690529729660039656131 36428535794594490059484197)
  ·
    refine ⟨6830350461486466886153287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36428535794594490059484197 6830350461486466886153287)
    ·
      refine ⟨10245525692229700329229931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830350461486466886153287 10245525692229700329229931)
      ·
        refine ⟨15368288538344550493844897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245525692229700329229931 15368288538344550493844897)
        ·
          refine ⟨11526216403758412870383673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15368288538344550493844897 11526216403758412870383673)
          ·
            refine ⟨8644662302818809652787755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11526216403758412870383673 8644662302818809652787755)
            ·
              refine ⟨12966993454228214479181633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8644662302818809652787755 12966993454228214479181633)
              ·
                refine ⟨9725245090671160859386225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12966993454228214479181633 9725245090671160859386225)
                ·
                  refine ⟨7293933818003370644539669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9725245090671160859386225 7293933818003370644539669)
                  ·
                    refine ⟨341903147718907998962797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7293933818003370644539669 341903147718907998962797)
                    ·
                      rfl

theorem cell22_998781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_998781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998781 prefixEnd_998781 := by exact prefixLift 998781
  have htrace : WordTrace (prefixWord ++ tailWord_998781) baseStart_998781 baseEnd_998781 := by
    simpa [prefixWord, tailWord_998781, baseEnd_998781] using wordTrace_append hprefix tailTrace_998781
  have hstable : (prefixWord ++ tailWord_998781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998781).length < 2 ^ (prefixWord ++ tailWord_998781).sum := by decide
  have hdescent : baseEnd_998781 < baseStart_998781 := by decide
  rcases family_descends (prefixWord ++ tailWord_998781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998785 : List Nat := [1, 2, 4, 3, 2, 1, 3, 6]
def baseStart_998785 : Nat := 118140960795 + 998785 * 2 ^ 59
def prefixEnd_998785 : Nat := 4983230072969 + 3 ^ 40 * 998785 * 2
def baseEnd_998785 : Nat := 37989390777850369095865

theorem tailTrace_998785 : CollatzResearch.WordTrace tailWord_998785 prefixEnd_998785 37989390777850369095865 := by
  unfold tailWord_998785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36428681686579998742629809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24285787791053332495086539 36428681686579998742629809)
  ·
    refine ⟨27321511264934999056972357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36428681686579998742629809 27321511264934999056972357)
    ·
      refine ⟨5122783362175312323182317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27321511264934999056972357 5122783362175312323182317)
      ·
        refine ⟨1921043760815742121193369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5122783362175312323182317 1921043760815742121193369)
        ·
          refine ⟨1440782820611806590895027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1921043760815742121193369 1440782820611806590895027)
          ·
            refine ⟨2161174230917709886342541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440782820611806590895027 2161174230917709886342541)
            ·
              refine ⟨810440336594141207378453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2161174230917709886342541 810440336594141207378453)
              ·
                refine ⟨37989390777850369095865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 810440336594141207378453 37989390777850369095865)
                ·
                  rfl

theorem cell22_998785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 6].length) (baseStart_998785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998785 prefixEnd_998785 := by exact prefixLift 998785
  have htrace : WordTrace (prefixWord ++ tailWord_998785) baseStart_998785 baseEnd_998785 := by
    simpa [prefixWord, tailWord_998785, baseEnd_998785] using wordTrace_append hprefix tailTrace_998785
  have hstable : (prefixWord ++ tailWord_998785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998785).length < 2 ^ (prefixWord ++ tailWord_998785).sum := by decide
  have hdescent : baseEnd_998785 < baseStart_998785 := by decide
  rcases family_descends (prefixWord ++ tailWord_998785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998796 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 7]
def baseStart_998796 : Nat := 118140960795 + 998796 * 2 ^ 59
def prefixEnd_998796 : Nat := 4983230072969 + 3 ^ 40 * 998796 * 2
def baseEnd_998796 : Nat := 113969427508484319945917

theorem tailTrace_998796 : CollatzResearch.WordTrace tailWord_998796 prefixEnd_998796 113969427508484319945917 := by
  unfold tailWord_998796
  simp only [CollatzResearch.WordTrace]
  refine ⟨18214541444770073810640121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24286055259693431747520161 18214541444770073810640121)
  ·
    refine ⟨13660906083577555357980091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18214541444770073810640121 13660906083577555357980091)
    ·
      refine ⟨20491359125366333036970137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13660906083577555357980091 20491359125366333036970137)
      ·
        refine ⟨15368519344024749777727603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20491359125366333036970137 15368519344024749777727603)
        ·
          refine ⟨23052779016037124666591405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15368519344024749777727603 23052779016037124666591405)
          ·
            refine ⟨8644792131013921749971777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23052779016037124666591405 8644792131013921749971777)
            ·
              refine ⟨6483594098260441312478833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8644792131013921749971777 6483594098260441312478833)
              ·
                refine ⟨4862695573695330984359125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483594098260441312478833 4862695573695330984359125)
                ·
                  refine ⟨113969427508484319945917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4862695573695330984359125 113969427508484319945917)
                  ·
                    rfl

theorem cell22_998796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_998796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998796 prefixEnd_998796 := by exact prefixLift 998796
  have htrace : WordTrace (prefixWord ++ tailWord_998796) baseStart_998796 baseEnd_998796 := by
    simpa [prefixWord, tailWord_998796, baseEnd_998796] using wordTrace_append hprefix tailTrace_998796
  have hstable : (prefixWord ++ tailWord_998796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998796).length < 2 ^ (prefixWord ++ tailWord_998796).sum := by decide
  have hdescent : baseEnd_998796 < baseStart_998796 := by decide
  rcases family_descends (prefixWord ++ tailWord_998796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998813 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 7]
def baseStart_998813 : Nat := 118140960795 + 998813 * 2 ^ 59
def prefixEnd_998813 : Nat := 4983230072969 + 3 ^ 40 * 998813 * 2
def baseEnd_998813 : Nat := 113971367324290194054233

theorem tailTrace_998813 : CollatzResearch.WordTrace tailWord_998813 prefixEnd_998813 113971367324290194054233 := by
  unfold tailWord_998813
  simp only [CollatzResearch.WordTrace]
  refine ⟨36429702930478559524649093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24286468620319039683099395 36429702930478559524649093)
  ·
    refine ⟨6830569299464729910871705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36429702930478559524649093 6830569299464729910871705)
    ·
      refine ⟨5122926974598547433153779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6830569299464729910871705 5122926974598547433153779)
      ·
        refine ⟨7684390461897821149730669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122926974598547433153779 7684390461897821149730669)
        ·
          refine ⟨2881646423211682931149001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7684390461897821149730669 2881646423211682931149001)
          ·
            refine ⟨2161234817408762198361751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2881646423211682931149001 2161234817408762198361751)
            ·
              refine ⟨3241852226113143297542627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161234817408762198361751 3241852226113143297542627)
              ·
                refine ⟨4862778339169714946313941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241852226113143297542627 4862778339169714946313941)
                ·
                  refine ⟨113971367324290194054233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4862778339169714946313941 113971367324290194054233)
                  ·
                    rfl

theorem cell22_998813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_998813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998813 prefixEnd_998813 := by exact prefixLift 998813
  have htrace : WordTrace (prefixWord ++ tailWord_998813) baseStart_998813 baseEnd_998813 := by
    simpa [prefixWord, tailWord_998813, baseEnd_998813] using wordTrace_append hprefix tailTrace_998813
  have hstable : (prefixWord ++ tailWord_998813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998813).length < 2 ^ (prefixWord ++ tailWord_998813).sum := by decide
  have hdescent : baseEnd_998813 < baseStart_998813 := by decide
  rcases family_descends (prefixWord ++ tailWord_998813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998860 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_998860 : Nat := 118140960795 + 998860 * 2 ^ 59
def prefixEnd_998860 : Nat := 4983230072969 + 3 ^ 40 * 998860 * 2
def baseEnd_998860 : Nat := 341930191033378126237555

theorem tailTrace_998860 : CollatzResearch.WordTrace tailWord_998860 prefixEnd_998860 341930191033378126237555 := by
  unfold tailWord_998860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18215708580654143275805017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24287611440872191034406689 18215708580654143275805017)
  ·
    refine ⟨13661781435490607456853763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18215708580654143275805017 13661781435490607456853763)
    ·
      refine ⟨20492672153235911185280645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13661781435490607456853763 20492672153235911185280645)
      ·
        refine ⟨3842376028731733347240121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20492672153235911185280645 3842376028731733347240121)
        ·
          refine ⟨2881782021548800010430091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3842376028731733347240121 2881782021548800010430091)
          ·
            refine ⟨4322673032323200015645137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881782021548800010430091 4322673032323200015645137)
            ·
              refine ⟨3242004774242400011733853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322673032323200015645137 3242004774242400011733853)
              ·
                refine ⟨1215751790340900004400195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3242004774242400011733853 1215751790340900004400195)
                ·
                  refine ⟨1823627685511350006600293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215751790340900004400195 1823627685511350006600293)
                  ·
                    refine ⟨341930191033378126237555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823627685511350006600293 341930191033378126237555)
                    ·
                      rfl

theorem cell22_998860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_998860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998860 prefixEnd_998860 := by exact prefixLift 998860
  have htrace : WordTrace (prefixWord ++ tailWord_998860) baseStart_998860 baseEnd_998860 := by
    simpa [prefixWord, tailWord_998860, baseEnd_998860] using wordTrace_append hprefix tailTrace_998860
  have hstable : (prefixWord ++ tailWord_998860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998860).length < 2 ^ (prefixWord ++ tailWord_998860).sum := by decide
  have hdescent : baseEnd_998860 < baseStart_998860 := by decide
  rcases family_descends (prefixWord ++ tailWord_998860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998888 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_998888 : Nat := 118140960795 + 998888 * 2 ^ 59
def prefixEnd_998888 : Nat := 4983230072969 + 3 ^ 40 * 998888 * 2
def baseEnd_998888 : Nat := 341939776005595386537469

theorem tailTrace_998888 : CollatzResearch.WordTrace tailWord_998888 prefixEnd_998888 341939776005595386537469 := by
  unfold tailWord_998888
  simp only [CollatzResearch.WordTrace]
  refine ⟨18216219202603423666814659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24288292270137898222419545 18216219202603423666814659)
  ·
    refine ⟨27324328803905135500221989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18216219202603423666814659 27324328803905135500221989)
    ·
      refine ⟨5123311650732212906291623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27324328803905135500221989 5123311650732212906291623)
      ·
        refine ⟨7684967476098319359437435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123311650732212906291623 7684967476098319359437435)
        ·
          refine ⟨11527451214147479039156153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684967476098319359437435 11527451214147479039156153)
          ·
            refine ⟨8645588410610609279367115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11527451214147479039156153 8645588410610609279367115)
            ·
              refine ⟨12968382615915913919050673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8645588410610609279367115 12968382615915913919050673)
              ·
                refine ⟨9726286961936935439288005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12968382615915913919050673 9726286961936935439288005)
                ·
                  refine ⟨1823678805363175394866501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9726286961936935439288005 1823678805363175394866501)
                  ·
                    refine ⟨341939776005595386537469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823678805363175394866501 341939776005595386537469)
                    ·
                      rfl

theorem cell22_998888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_998888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998888 prefixEnd_998888 := by exact prefixLift 998888
  have htrace : WordTrace (prefixWord ++ tailWord_998888) baseStart_998888 baseEnd_998888 := by
    simpa [prefixWord, tailWord_998888, baseEnd_998888] using wordTrace_append hprefix tailTrace_998888
  have hstable : (prefixWord ++ tailWord_998888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998888).length < 2 ^ (prefixWord ++ tailWord_998888).sum := by decide
  have hdescent : baseEnd_998888 < baseStart_998888 := by decide
  rcases family_descends (prefixWord ++ tailWord_998888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998926 : List Nat := [4, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_998926 : Nat := 118140960795 + 998926 * 2 ^ 59
def prefixEnd_998926 : Nat := 4983230072969 + 3 ^ 40 * 998926 * 2
def baseEnd_998926 : Nat := 113984261394058651362451

theorem tailTrace_998926 : CollatzResearch.WordTrace tailWord_998926 prefixEnd_998926 113984261394058651362451 := by
  unfold tailWord_998926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554228047383647477939079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24289216252712786549008421 4554228047383647477939079)
  ·
    refine ⟨6831342071075471216908619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4554228047383647477939079 6831342071075471216908619)
    ·
      refine ⟨10247013106613206825362929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6831342071075471216908619 10247013106613206825362929)
      ·
        refine ⟨7685259829959905119022197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10247013106613206825362929 7685259829959905119022197)
        ·
          refine ⟨720493109058741104908331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7685259829959905119022197 720493109058741104908331)
          ·
            refine ⟨1080739663588111657362497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720493109058741104908331 1080739663588111657362497)
            ·
              refine ⟨810554747691083743021873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080739663588111657362497 810554747691083743021873)
              ·
                refine ⟨607916060768312807266405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810554747691083743021873 607916060768312807266405)
                ·
                  refine ⟨113984261394058651362451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607916060768312807266405 113984261394058651362451)
                  ·
                    rfl

theorem cell22_998926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_998926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998926 prefixEnd_998926 := by exact prefixLift 998926
  have htrace : WordTrace (prefixWord ++ tailWord_998926) baseStart_998926 baseEnd_998926 := by
    simpa [prefixWord, tailWord_998926, baseEnd_998926] using wordTrace_append hprefix tailTrace_998926
  have hstable : (prefixWord ++ tailWord_998926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998926).length < 2 ^ (prefixWord ++ tailWord_998926).sum := by decide
  have hdescent : baseEnd_998926 < baseStart_998926 := by decide
  rcases family_descends (prefixWord ++ tailWord_998926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998933 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_998933 : Nat := 118140960795 + 998933 * 2 ^ 59
def prefixEnd_998933 : Nat := 4983230072969 + 3 ^ 40 * 998933 * 2
def baseEnd_998933 : Nat := 341955180425230269162331

theorem tailTrace_998933 : CollatzResearch.WordTrace tailWord_998933 prefixEnd_998933 341955180425230269162331 := by
  unfold tailWord_998933
  simp only [CollatzResearch.WordTrace]
  refine ⟨36434079690043820019017453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24289386460029213346011635 36434079690043820019017453)
  ·
    refine ⟨13662779883766432507131545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36434079690043820019017453 13662779883766432507131545)
    ·
      refine ⟨10247084912824824380348659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13662779883766432507131545 10247084912824824380348659)
      ·
        refine ⟨15370627369237236570522989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247084912824824380348659 15370627369237236570522989)
        ·
          refine ⟨5763985263463963713946121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15370627369237236570522989 5763985263463963713946121)
          ·
            refine ⟨4322988947597972785459591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5763985263463963713946121 4322988947597972785459591)
            ·
              refine ⟨6484483421396959178189387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322988947597972785459591 6484483421396959178189387)
              ·
                refine ⟨9726725132095438767284081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484483421396959178189387 9726725132095438767284081)
                ·
                  refine ⟨7295043849071579075463061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9726725132095438767284081 7295043849071579075463061)
                  ·
                    refine ⟨341955180425230269162331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7295043849071579075463061 341955180425230269162331)
                    ·
                      rfl

theorem cell22_998933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_998933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998933 prefixEnd_998933 := by exact prefixLift 998933
  have htrace : WordTrace (prefixWord ++ tailWord_998933) baseStart_998933 baseEnd_998933 := by
    simpa [prefixWord, tailWord_998933, baseEnd_998933] using wordTrace_append hprefix tailTrace_998933
  have hstable : (prefixWord ++ tailWord_998933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998933).length < 2 ^ (prefixWord ++ tailWord_998933).sum := by decide
  have hdescent : baseEnd_998933 < baseStart_998933 := by decide
  rcases family_descends (prefixWord ++ tailWord_998933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998969 : List Nat := [1, 2, 1, 5, 1, 3, 2, 3, 1, 3]
def baseStart_998969 : Nat := 118140960795 + 998969 * 2 ^ 59
def prefixEnd_998969 : Nat := 4983230072969 + 3 ^ 40 * 998969 * 2
def baseEnd_998969 : Nat := 341967503960938175262221

theorem tailTrace_998969 : CollatzResearch.WordTrace tailWord_998969 prefixEnd_998969 341967503960938175262221 := by
  unfold tailWord_998969
  simp only [CollatzResearch.WordTrace]
  refine ⟨36435392717913398167327961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24290261811942265444885307 36435392717913398167327961)
  ·
    refine ⟨27326544538435048625495971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36435392717913398167327961 27326544538435048625495971)
    ·
      refine ⟨40989816807652572938243957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27326544538435048625495971 40989816807652572938243957)
      ·
        refine ⟨3842795325717428712960371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40989816807652572938243957 3842795325717428712960371)
        ·
          refine ⟨5764192988576143069440557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842795325717428712960371 5764192988576143069440557)
          ·
            refine ⟨2161572370716053651040209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5764192988576143069440557 2161572370716053651040209)
            ·
              refine ⟨1621179278037040238280157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161572370716053651040209 1621179278037040238280157)
              ·
                refine ⟨607942229263890089355059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1621179278037040238280157 607942229263890089355059)
                ·
                  refine ⟨911913343895835134032589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 607942229263890089355059 911913343895835134032589)
                  ·
                    refine ⟨341967503960938175262221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 911913343895835134032589 341967503960938175262221)
                    ·
                      rfl

theorem cell22_998969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 3].length) (baseStart_998969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_998969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_998969 prefixEnd_998969 := by exact prefixLift 998969
  have htrace : WordTrace (prefixWord ++ tailWord_998969) baseStart_998969 baseEnd_998969 := by
    simpa [prefixWord, tailWord_998969, baseEnd_998969] using wordTrace_append hprefix tailTrace_998969
  have hstable : (prefixWord ++ tailWord_998969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998969).length < 2 ^ (prefixWord ++ tailWord_998969).sum := by decide
  have hdescent : baseEnd_998969 < baseStart_998969 := by decide
  rcases family_descends (prefixWord ++ tailWord_998969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999012 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_999012 : Nat := 118140960795 + 999012 * 2 ^ 59
def prefixEnd_999012 : Nat := 4983230072969 + 3 ^ 40 * 999012 * 2
def baseEnd_999012 : Nat := 341982223739700396437089

theorem tailTrace_999012 : CollatzResearch.WordTrace tailWord_999012 prefixEnd_999012 341982223739700396437089 := by
  unfold tailWord_999012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18218480528378808255571645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24291307371171744340762193 18218480528378808255571645)
  ·
    refine ⟨6831930198142053095839367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18218480528378808255571645 6831930198142053095839367)
    ·
      refine ⟨10247895297213079643759051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6831930198142053095839367 10247895297213079643759051)
      ·
        refine ⟨15371842945819619465638577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247895297213079643759051 15371842945819619465638577)
        ·
          refine ⟨11528882209364714599228933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15371842945819619465638577 11528882209364714599228933)
          ·
            refine ⟨2161665414255883987355425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11528882209364714599228933 2161665414255883987355425)
            ·
              refine ⟨1621249060691912990516569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161665414255883987355425 1621249060691912990516569)
              ·
                refine ⟨1215936795518934742887427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621249060691912990516569 1215936795518934742887427)
                ·
                  refine ⟨1823905193278402114331141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215936795518934742887427 1823905193278402114331141)
                  ·
                    refine ⟨341982223739700396437089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823905193278402114331141 341982223739700396437089)
                    ·
                      rfl

theorem cell22_999012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_999012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999012 prefixEnd_999012 := by exact prefixLift 999012
  have htrace : WordTrace (prefixWord ++ tailWord_999012) baseStart_999012 baseEnd_999012 := by
    simpa [prefixWord, tailWord_999012, baseEnd_999012] using wordTrace_append hprefix tailTrace_999012
  have hstable : (prefixWord ++ tailWord_999012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999012).length < 2 ^ (prefixWord ++ tailWord_999012).sum := by decide
  have hdescent : baseEnd_999012 < baseStart_999012 := by decide
  rcases family_descends (prefixWord ++ tailWord_999012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999040 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_999040 : Nat := 118140960795 + 999040 * 2 ^ 59
def prefixEnd_999040 : Nat := 4983230072969 + 3 ^ 40 * 999040 * 2
def baseEnd_999040 : Nat := 341991808711917656737003

theorem tailTrace_999040 : CollatzResearch.WordTrace tailWord_999040 prefixEnd_999040 341991808711917656737003 := by
  unfold tailWord_999040
  simp only [CollatzResearch.WordTrace]
  refine ⟨18218991150328088646581287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24291988200437451528775049 18218991150328088646581287)
  ·
    refine ⟨27328486725492132969871931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18218991150328088646581287 27328486725492132969871931)
    ·
      refine ⟨40992730088238199454807897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27328486725492132969871931 40992730088238199454807897)
      ·
        refine ⟨30744547566178649591105923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40992730088238199454807897 30744547566178649591105923)
        ·
          refine ⟨46116821349267974386658885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30744547566178649591105923 46116821349267974386658885)
          ·
            refine ⟨8646904002987745197498541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46116821349267974386658885 8646904002987745197498541)
            ·
              refine ⟨3242589001120404449061953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8646904002987745197498541 3242589001120404449061953)
              ·
                refine ⟨2431941750840303336796465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3242589001120404449061953 2431941750840303336796465)
                ·
                  refine ⟨1823956313130227502597349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2431941750840303336796465 1823956313130227502597349)
                  ·
                    refine ⟨341991808711917656737003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823956313130227502597349 341991808711917656737003)
                    ·
                      rfl

theorem cell22_999040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_999040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999040 prefixEnd_999040 := by exact prefixLift 999040
  have htrace : WordTrace (prefixWord ++ tailWord_999040) baseStart_999040 baseEnd_999040 := by
    simpa [prefixWord, tailWord_999040, baseEnd_999040] using wordTrace_append hprefix tailTrace_999040
  have hstable : (prefixWord ++ tailWord_999040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999040).length < 2 ^ (prefixWord ++ tailWord_999040).sum := by decide
  have hdescent : baseEnd_999040 < baseStart_999040 := by decide
  rcases family_descends (prefixWord ++ tailWord_999040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999044 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 6]
def baseStart_999044 : Nat := 118140960795 + 999044 * 2 ^ 59
def prefixEnd_999044 : Nat := 4983230072969 + 3 ^ 40 * 999044 * 2
def baseEnd_999044 : Nat := 113997725997887659878997

theorem tailTrace_999044 : CollatzResearch.WordTrace tailWord_999044 prefixEnd_999044 113997725997887659878997 := by
  unfold tailWord_999044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18219064096320842988154093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24292085461761123984205457 18219064096320842988154093)
  ·
    refine ⟨6832149036120316120557785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18219064096320842988154093 6832149036120316120557785)
    ·
      refine ⟨5124111777090237090418339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6832149036120316120557785 5124111777090237090418339)
      ·
        refine ⟨7686167665635355635627509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124111777090237090418339 7686167665635355635627509)
        ·
          refine ⟨720578218653314590840079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7686167665635355635627509 720578218653314590840079)
          ·
            refine ⟨1080867327979971886260119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720578218653314590840079 1080867327979971886260119)
            ·
              refine ⟨1621300991969957829390179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080867327979971886260119 1621300991969957829390179)
              ·
                refine ⟨2431951487954936744085269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621300991969957829390179 2431951487954936744085269)
                ·
                  refine ⟨113997725997887659878997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2431951487954936744085269 113997725997887659878997)
                  ·
                    rfl

theorem cell22_999044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_999044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999044 prefixEnd_999044 := by exact prefixLift 999044
  have htrace : WordTrace (prefixWord ++ tailWord_999044) baseStart_999044 baseEnd_999044 := by
    simpa [prefixWord, tailWord_999044, baseEnd_999044] using wordTrace_append hprefix tailTrace_999044
  have hstable : (prefixWord ++ tailWord_999044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999044).length < 2 ^ (prefixWord ++ tailWord_999044).sum := by decide
  have hdescent : baseEnd_999044 < baseStart_999044 := by decide
  rcases family_descends (prefixWord ++ tailWord_999044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999104 : List Nat := [2, 1, 1, 2, 4, 1, 3, 4, 1, 3]
def baseStart_999104 : Nat := 118140960795 + 999104 * 2 ^ 59
def prefixEnd_999104 : Nat := 4983230072969 + 3 ^ 40 * 999104 * 2
def baseEnd_999104 : Nat := 342013717219842823136807

theorem tailTrace_999104 : CollatzResearch.WordTrace tailWord_999104 prefixEnd_999104 342013717219842823136807 := by
  unfold tailWord_999104
  simp only [CollatzResearch.WordTrace]
  refine ⟨18220158286212158111746183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24293544381616210815661577 18220158286212158111746183)
  ·
    refine ⟨27330237429318237167619275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18220158286212158111746183 27330237429318237167619275)
    ·
      refine ⟨40995356143977355751428913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27330237429318237167619275 40995356143977355751428913)
      ·
        refine ⟨30746517107983016813571685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40995356143977355751428913 30746517107983016813571685)
        ·
          refine ⟨5764971957746815652544691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30746517107983016813571685 5764971957746815652544691)
          ·
            refine ⟨8647457936620223478817037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764971957746815652544691 8647457936620223478817037)
            ·
              refine ⟨3242796726232583804556389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8647457936620223478817037 3242796726232583804556389)
              ·
                refine ⟨608024386168609463354323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3242796726232583804556389 608024386168609463354323)
                ·
                  refine ⟨912036579252914195031485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608024386168609463354323 912036579252914195031485)
                  ·
                    refine ⟨342013717219842823136807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912036579252914195031485 342013717219842823136807)
                    ·
                      rfl

theorem cell22_999104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 3].length) (baseStart_999104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999104 prefixEnd_999104 := by exact prefixLift 999104
  have htrace : WordTrace (prefixWord ++ tailWord_999104) baseStart_999104 baseEnd_999104 := by
    simpa [prefixWord, tailWord_999104, baseEnd_999104] using wordTrace_append hprefix tailTrace_999104
  have hstable : (prefixWord ++ tailWord_999104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999104).length < 2 ^ (prefixWord ++ tailWord_999104).sum := by decide
  have hdescent : baseEnd_999104 < baseStart_999104 := by decide
  rcases family_descends (prefixWord ++ tailWord_999104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999316 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_999316 : Nat := 118140960795 + 999316 * 2 ^ 59
def prefixEnd_999316 : Nat := 4983230072969 + 3 ^ 40 * 999316 * 2
def baseEnd_999316 : Nat := 342086289152344936836157

theorem tailTrace_999316 : CollatzResearch.WordTrace tailWord_999316 prefixEnd_999316 342086289152344936836157 := by
  unfold tailWord_999316
  simp only [CollatzResearch.WordTrace]
  refine ⟨18224024423828138215104901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24298699231770850953473201 18224024423828138215104901)
  ·
    refine ⟨3417004579467775915332169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18224024423828138215104901 3417004579467775915332169)
    ·
      refine ⟨2562753434600831936499127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3417004579467775915332169 2562753434600831936499127)
      ·
        refine ⟨3844130151901247904748691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2562753434600831936499127 3844130151901247904748691)
        ·
          refine ⟨5766195227851871857123037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844130151901247904748691 5766195227851871857123037)
          ·
            refine ⟨2162323210444451946421139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5766195227851871857123037 2162323210444451946421139)
            ·
              refine ⟨3243484815666677919631709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162323210444451946421139 3243484815666677919631709)
              ·
                refine ⟨1216306805875004219861891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3243484815666677919631709 1216306805875004219861891)
                ·
                  refine ⟨1824460208812506329792837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216306805875004219861891 1824460208812506329792837)
                  ·
                    refine ⟨342086289152344936836157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1824460208812506329792837 342086289152344936836157)
                    ·
                      rfl

theorem cell22_999316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_999316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999316 prefixEnd_999316 := by exact prefixLift 999316
  have htrace : WordTrace (prefixWord ++ tailWord_999316) baseStart_999316 baseEnd_999316 := by
    simpa [prefixWord, tailWord_999316, baseEnd_999316] using wordTrace_append hprefix tailTrace_999316
  have hstable : (prefixWord ++ tailWord_999316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999316).length < 2 ^ (prefixWord ++ tailWord_999316).sum := by decide
  have hdescent : baseEnd_999316 < baseStart_999316 := by decide
  rcases family_descends (prefixWord ++ tailWord_999316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999391 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 3, 3]
def baseStart_999391 : Nat := 118140960795 + 999391 * 2 ^ 59
def prefixEnd_999391 : Nat := 4983230072969 + 3 ^ 40 * 999391 * 2
def baseEnd_999391 : Nat := 342111963185069741210927

theorem tailTrace_999391 : CollatzResearch.WordTrace tailWord_999391 prefixEnd_999391 342111963185069741210927 := by
  unfold tailWord_999391
  simp only [CollatzResearch.WordTrace]
  refine ⟨36450784322384564239190027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24300522881589709492793351 36450784322384564239190027)
  ·
    refine ⟨54676176483576846358785041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36450784322384564239190027 54676176483576846358785041)
    ·
      refine ⟨41007132362682634769088781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54676176483576846358785041 41007132362682634769088781)
      ·
        refine ⟨15377674636005988038408293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41007132362682634769088781 15377674636005988038408293)
        ·
          refine ⟨2883313994251122757201555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15377674636005988038408293 2883313994251122757201555)
          ·
            refine ⟨4324970991376684135802333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883313994251122757201555 4324970991376684135802333)
            ·
              refine ⟨1621864121766256550925875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4324970991376684135802333 1621864121766256550925875)
              ·
                refine ⟨2432796182649384826388813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621864121766256550925875 2432796182649384826388813)
                ·
                  refine ⟨912298568493519309895805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2432796182649384826388813 912298568493519309895805)
                  ·
                    refine ⟨342111963185069741210927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912298568493519309895805 342111963185069741210927)
                    ·
                      rfl

theorem cell22_999391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_999391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999391 prefixEnd_999391 := by exact prefixLift 999391
  have htrace : WordTrace (prefixWord ++ tailWord_999391) baseStart_999391 baseEnd_999391 := by
    simpa [prefixWord, tailWord_999391, baseEnd_999391] using wordTrace_append hprefix tailTrace_999391
  have hstable : (prefixWord ++ tailWord_999391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999391).length < 2 ^ (prefixWord ++ tailWord_999391).sum := by decide
  have hdescent : baseEnd_999391 < baseStart_999391 := by decide
  rcases family_descends (prefixWord ++ tailWord_999391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999466 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_999466 : Nat := 118140960795 + 999466 * 2 ^ 59
def prefixEnd_999466 : Nat := 4983230072969 + 3 ^ 40 * 999466 * 2
def baseEnd_999466 : Nat := 114045879072598181861899

theorem tailTrace_999466 : CollatzResearch.WordTrace tailWord_999466 prefixEnd_999466 114045879072598181861899 := by
  unfold tailWord_999466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113379949278213012042563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24302346531408568032113501 9113379949278213012042563)
  ·
    refine ⟨13670069923917319518063845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9113379949278213012042563 13670069923917319518063845)
    ·
      refine ⟨2563138110734497409636971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13670069923917319518063845 2563138110734497409636971)
      ·
        refine ⟨3844707166101746114455457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2563138110734497409636971 3844707166101746114455457)
        ·
          refine ⟨2883530374576309585841593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3844707166101746114455457 2883530374576309585841593)
          ·
            refine ⟨2162647780932232189381195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2883530374576309585841593 2162647780932232189381195)
            ·
              refine ⟨3243971671398348284071793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162647780932232189381195 3243971671398348284071793)
              ·
                refine ⟨2432978753548761213053845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3243971671398348284071793 2432978753548761213053845)
                ·
                  refine ⟨114045879072598181861899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2432978753548761213053845 114045879072598181861899)
                  ·
                    rfl

theorem cell22_999466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_999466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999466 prefixEnd_999466 := by exact prefixLift 999466
  have htrace : WordTrace (prefixWord ++ tailWord_999466) baseStart_999466 baseEnd_999466 := by
    simpa [prefixWord, tailWord_999466, baseEnd_999466] using wordTrace_append hprefix tailTrace_999466
  have hstable : (prefixWord ++ tailWord_999466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999466).length < 2 ^ (prefixWord ++ tailWord_999466).sum := by decide
  have hdescent : baseEnd_999466 < baseStart_999466 := by decide
  rcases family_descends (prefixWord ++ tailWord_999466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999524 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_999524 : Nat := 118140960795 + 999524 * 2 ^ 59
def prefixEnd_999524 : Nat := 4983230072969 + 3 ^ 40 * 999524 * 2
def baseEnd_999524 : Nat := 342157491803101727635519

theorem tailTrace_999524 : CollatzResearch.WordTrace tailWord_999524 prefixEnd_999524 342157491803101727635519 := by
  unfold tailWord_999524
  simp only [CollatzResearch.WordTrace]
  refine ⟨18227817615451363976890813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24303756820601818635854417 18227817615451363976890813)
  ·
    refine ⟨6835431605794261491334055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18227817615451363976890813 6835431605794261491334055)
    ·
      refine ⟨10253147408691392237001083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6835431605794261491334055 10253147408691392237001083)
      ·
        refine ⟨15379721113037088355501625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253147408691392237001083 15379721113037088355501625)
        ·
          refine ⟨11534790834777816266626219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15379721113037088355501625 11534790834777816266626219)
          ·
            refine ⟨17302186252166724399939329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534790834777816266626219 17302186252166724399939329)
            ·
              refine ⟨12976639689125043299954497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17302186252166724399939329 12976639689125043299954497)
              ·
                refine ⟨9732479766843782474965873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12976639689125043299954497 9732479766843782474965873)
                ·
                  refine ⟨7299359825132836856224405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9732479766843782474965873 7299359825132836856224405)
                  ·
                    refine ⟨342157491803101727635519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7299359825132836856224405 342157491803101727635519)
                    ·
                      rfl

theorem cell22_999524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_999524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999524 prefixEnd_999524 := by exact prefixLift 999524
  have htrace : WordTrace (prefixWord ++ tailWord_999524) baseStart_999524 baseEnd_999524 := by
    simpa [prefixWord, tailWord_999524, baseEnd_999524] using wordTrace_append hprefix tailTrace_999524
  have hstable : (prefixWord ++ tailWord_999524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999524).length < 2 ^ (prefixWord ++ tailWord_999524).sum := by decide
  have hdescent : baseEnd_999524 < baseStart_999524 := by decide
  rcases family_descends (prefixWord ++ tailWord_999524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999556 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 5]
def baseStart_999556 : Nat := 118140960795 + 999556 * 2 ^ 59
def prefixEnd_999556 : Nat := 4983230072969 + 3 ^ 40 * 999556 * 2
def baseEnd_999556 : Nat := 114056148685688103611807

theorem tailTrace_999556 : CollatzResearch.WordTrace tailWord_999556 prefixEnd_999556 114056148685688103611807 := by
  unfold tailWord_999556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18228401183393398709473261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24304534911191198279297681 18228401183393398709473261)
  ·
    refine ⟨6835650443772524516052473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18228401183393398709473261 6835650443772524516052473)
    ·
      refine ⟨5126737832829393387039355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6835650443772524516052473 5126737832829393387039355)
      ·
        refine ⟨7690106749244090080559033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126737832829393387039355 7690106749244090080559033)
        ·
          refine ⟨5767580061933067560419275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7690106749244090080559033 5767580061933067560419275)
          ·
            refine ⟨8651370092899601340628913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767580061933067560419275 8651370092899601340628913)
            ·
              refine ⟨6488527569674701005471685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8651370092899601340628913 6488527569674701005471685)
              ·
                refine ⟨1216598919314006438525941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6488527569674701005471685 1216598919314006438525941)
                ·
                  refine ⟨114056148685688103611807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1216598919314006438525941 114056148685688103611807)
                  ·
                    rfl

theorem cell22_999556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_999556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999556 prefixEnd_999556 := by exact prefixLift 999556
  have htrace : WordTrace (prefixWord ++ tailWord_999556) baseStart_999556 baseEnd_999556 := by
    simpa [prefixWord, tailWord_999556, baseEnd_999556] using wordTrace_append hprefix tailTrace_999556
  have hstable : (prefixWord ++ tailWord_999556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999556).length < 2 ^ (prefixWord ++ tailWord_999556).sum := by decide
  have hdescent : baseEnd_999556 < baseStart_999556 := by decide
  rcases family_descends (prefixWord ++ tailWord_999556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999560 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 3, 3]
def baseStart_999560 : Nat := 118140960795 + 999560 * 2 ^ 59
def prefixEnd_999560 : Nat := 4983230072969 + 3 ^ 40 * 999560 * 2
def baseEnd_999560 : Nat := 342169815338809633735409

theorem tailTrace_999560 : CollatzResearch.WordTrace tailWord_999560 prefixEnd_999560 342169815338809633735409 := by
  unfold tailWord_999560
  simp only [CollatzResearch.WordTrace]
  refine ⟨18228474129386153051046067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24304632172514870734728089 18228474129386153051046067)
  ·
    refine ⟨27342711194079229576569101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18228474129386153051046067 27342711194079229576569101)
    ·
      refine ⟨10253516697779711091213413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27342711194079229576569101 10253516697779711091213413)
      ·
        refine ⟨1922534380833695829602515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10253516697779711091213413 1922534380833695829602515)
        ·
          refine ⟨2883801571250543744403773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922534380833695829602515 2883801571250543744403773)
          ·
            refine ⟨1081425589218953904151415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2883801571250543744403773 1081425589218953904151415)
            ·
              refine ⟨1622138383828430856227123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081425589218953904151415 1622138383828430856227123)
              ·
                refine ⟨2433207575742646284340685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622138383828430856227123 2433207575742646284340685)
                ·
                  refine ⟨912452840903492356627757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2433207575742646284340685 912452840903492356627757)
                  ·
                    refine ⟨342169815338809633735409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912452840903492356627757 342169815338809633735409)
                    ·
                      rfl

theorem cell22_999560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_999560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999560 prefixEnd_999560 := by exact prefixLift 999560
  have htrace : WordTrace (prefixWord ++ tailWord_999560) baseStart_999560 baseEnd_999560 := by
    simpa [prefixWord, tailWord_999560, baseEnd_999560] using wordTrace_append hprefix tailTrace_999560
  have hstable : (prefixWord ++ tailWord_999560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999560).length < 2 ^ (prefixWord ++ tailWord_999560).sum := by decide
  have hdescent : baseEnd_999560 < baseStart_999560 := by decide
  rcases family_descends (prefixWord ++ tailWord_999560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999633 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 2, 3]
def baseStart_999633 : Nat := 118140960795 + 999633 * 2 ^ 59
def prefixEnd_999633 : Nat := 4983230072969 + 3 ^ 40 * 999633 * 2
def baseEnd_999633 : Nat := 342194804730661776660185

theorem tailTrace_999633 : CollatzResearch.WordTrace tailWord_999633 prefixEnd_999633 342194804730661776660185 := by
  unfold tailWord_999633
  simp only [CollatzResearch.WordTrace]
  refine ⟨36459610787507839569499553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24306407191671893046333035 36459610787507839569499553)
  ·
    refine ⟨27344708090630879677124665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36459610787507839569499553 27344708090630879677124665)
    ·
      refine ⟨20508531067973159757843499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27344708090630879677124665 20508531067973159757843499)
      ·
        refine ⟨30762796601959739636765249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20508531067973159757843499 30762796601959739636765249)
        ·
          refine ⟨23072097451469804727573937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30762796601959739636765249 23072097451469804727573937)
          ·
            refine ⟨17304073088602353545680453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23072097451469804727573937 17304073088602353545680453)
            ·
              refine ⟨3244513704112941289815085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17304073088602353545680453 3244513704112941289815085)
              ·
                refine ⟨1216692639042352983680657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3244513704112941289815085 1216692639042352983680657)
                ·
                  refine ⟨912519479281764737760493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1216692639042352983680657 912519479281764737760493)
                  ·
                    refine ⟨342194804730661776660185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912519479281764737760493 342194804730661776660185)
                    ·
                      rfl

theorem cell22_999633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_999633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999633 prefixEnd_999633 := by exact prefixLift 999633
  have htrace : WordTrace (prefixWord ++ tailWord_999633) baseStart_999633 baseEnd_999633 := by
    simpa [prefixWord, tailWord_999633, baseEnd_999633] using wordTrace_append hprefix tailTrace_999633
  have hstable : (prefixWord ++ tailWord_999633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999633).length < 2 ^ (prefixWord ++ tailWord_999633).sum := by decide
  have hdescent : baseEnd_999633 < baseStart_999633 := by decide
  rcases family_descends (prefixWord ++ tailWord_999633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999712 : List Nat := [2, 1, 1, 5, 2, 1, 3, 3, 1, 3]
def baseStart_999712 : Nat := 118140960795 + 999712 * 2 ^ 59
def prefixEnd_999712 : Nat := 4983230072969 + 3 ^ 40 * 999712 * 2
def baseEnd_999712 : Nat := 342221848045131903934943

theorem tailTrace_999712 : CollatzResearch.WordTrace tailWord_999712 prefixEnd_999712 342221848045131903934943 := by
  unfold tailWord_999712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18231246077110818030812695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24308328102814424041083593 18231246077110818030812695)
  ·
    refine ⟨27346869115666227046219043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18231246077110818030812695 27346869115666227046219043)
    ·
      refine ⟨41020303673499340569328565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27346869115666227046219043 41020303673499340569328565)
      ·
        refine ⟨3845653469390563178374553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41020303673499340569328565 3845653469390563178374553)
        ·
          refine ⟨2884240102042922383780915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3845653469390563178374553 2884240102042922383780915)
          ·
            refine ⟨4326360153064383575671373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884240102042922383780915 4326360153064383575671373)
            ·
              refine ⟨1622385057399143840876765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4326360153064383575671373 1622385057399143840876765)
              ·
                refine ⟨608394396524678940328787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1622385057399143840876765 608394396524678940328787)
                ·
                  refine ⟨912591594787018410493181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608394396524678940328787 912591594787018410493181)
                  ·
                    refine ⟨342221848045131903934943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912591594787018410493181 342221848045131903934943)
                    ·
                      rfl

theorem cell22_999712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 3].length) (baseStart_999712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999712 prefixEnd_999712 := by exact prefixLift 999712
  have htrace : WordTrace (prefixWord ++ tailWord_999712) baseStart_999712 baseEnd_999712 := by
    simpa [prefixWord, tailWord_999712, baseEnd_999712] using wordTrace_append hprefix tailTrace_999712
  have hstable : (prefixWord ++ tailWord_999712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999712).length < 2 ^ (prefixWord ++ tailWord_999712).sum := by decide
  have hdescent : baseEnd_999712 < baseStart_999712 := by decide
  rcases family_descends (prefixWord ++ tailWord_999712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999729 : List Nat := [1, 2, 2, 3, 4, 1, 3, 2, 1, 3]
def baseStart_999729 : Nat := 118140960795 + 999729 * 2 ^ 59
def prefixEnd_999729 : Nat := 4983230072969 + 3 ^ 40 * 999729 * 2
def baseEnd_999729 : Nat := 342227667492549526259891

theorem tailTrace_999729 : CollatzResearch.WordTrace tailWord_999729 prefixEnd_999729 342227667492549526259891 := by
  unfold tailWord_999729
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463112195160047964994241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24308741463440031976662827 36463112195160047964994241)
  ·
    refine ⟨27347334146370035973745681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36463112195160047964994241 27347334146370035973745681)
    ·
      refine ⟨20510500609777526980309261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27347334146370035973745681 20510500609777526980309261)
      ·
        refine ⟨7691437728666572617615973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20510500609777526980309261 7691437728666572617615973)
        ·
          refine ⟨1442144574124982365802995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7691437728666572617615973 1442144574124982365802995)
          ·
            refine ⟨2163216861187473548704493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442144574124982365802995 2163216861187473548704493)
            ·
              refine ⟨811206322945302580764185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2163216861187473548704493 811206322945302580764185)
              ·
                refine ⟨608404742208976935573139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811206322945302580764185 608404742208976935573139)
                ·
                  refine ⟨912607113313465403359709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608404742208976935573139 912607113313465403359709)
                  ·
                    refine ⟨342227667492549526259891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912607113313465403359709 342227667492549526259891)
                    ·
                      rfl

theorem cell22_999729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_999729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999729 prefixEnd_999729 := by exact prefixLift 999729
  have htrace : WordTrace (prefixWord ++ tailWord_999729) baseStart_999729 baseEnd_999729 := by
    simpa [prefixWord, tailWord_999729, baseEnd_999729] using wordTrace_append hprefix tailTrace_999729
  have hstable : (prefixWord ++ tailWord_999729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999729).length < 2 ^ (prefixWord ++ tailWord_999729).sum := by decide
  have hdescent : baseEnd_999729 < baseStart_999729 := by decide
  rcases family_descends (prefixWord ++ tailWord_999729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999742 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_999742 : Nat := 118140960795 + 999742 * 2 ^ 59
def prefixEnd_999742 : Nat := 4983230072969 + 3 ^ 40 * 999742 * 2
def baseEnd_999742 : Nat := 114077372552740608561617

theorem tailTrace_999742 : CollatzResearch.WordTrace tailWord_999742 prefixEnd_999742 114077372552740608561617 := by
  unfold tailWord_999742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557948293014118898152185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24309057562741967456811653 4557948293014118898152185)
  ·
    refine ⟨3418461219760589173614139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4557948293014118898152185 3418461219760589173614139)
    ·
      refine ⟨5127691829640883760421209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3418461219760589173614139 5127691829640883760421209)
      ·
        refine ⟨3845768872230662820315907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5127691829640883760421209 3845768872230662820315907)
        ·
          refine ⟨5768653308345994230473861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845768872230662820315907 5768653308345994230473861)
          ·
            refine ⟨1081622495314873918213849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5768653308345994230473861 1081622495314873918213849)
            ·
              refine ⟨811216871486155438660387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081622495314873918213849 811216871486155438660387)
              ·
                refine ⟨1216825307229233157990581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811216871486155438660387 1216825307229233157990581)
                ·
                  refine ⟨114077372552740608561617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1216825307229233157990581 114077372552740608561617)
                  ·
                    rfl

theorem cell22_999742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_999742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999742 prefixEnd_999742 := by exact prefixLift 999742
  have htrace : WordTrace (prefixWord ++ tailWord_999742) baseStart_999742 baseEnd_999742 := by
    simpa [prefixWord, tailWord_999742, baseEnd_999742] using wordTrace_append hprefix tailTrace_999742
  have hstable : (prefixWord ++ tailWord_999742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999742).length < 2 ^ (prefixWord ++ tailWord_999742).sum := by decide
  have hdescent : baseEnd_999742 < baseStart_999742 := by decide
  rcases family_descends (prefixWord ++ tailWord_999742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999768 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 4, 3]
def baseStart_999768 : Nat := 118140960795 + 999768 * 2 ^ 59
def prefixEnd_999768 : Nat := 4983230072969 + 3 ^ 40 * 999768 * 2
def baseEnd_999768 : Nat := 342241017989566424534771

theorem tailTrace_999768 : CollatzResearch.WordTrace tailWord_999768 prefixEnd_999768 342241017989566424534771 := by
  unfold tailWord_999768
  simp only [CollatzResearch.WordTrace]
  refine ⟨18232267321009378812831979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24309689761345838417109305 18232267321009378812831979)
  ·
    refine ⟨27348400981514068219247969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18232267321009378812831979 27348400981514068219247969)
    ·
      refine ⟨20511300736135551164435977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27348400981514068219247969 20511300736135551164435977)
      ·
        refine ⟨15383475552101663373326983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20511300736135551164435977 15383475552101663373326983)
        ·
          refine ⟨23075213328152495059990475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15383475552101663373326983 23075213328152495059990475)
          ·
            refine ⟨34612819992228742589985713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23075213328152495059990475 34612819992228742589985713)
            ·
              refine ⟨25959614994171556942489285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34612819992228742589985713 25959614994171556942489285)
              ·
                refine ⟨4867427811407166926716741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25959614994171556942489285 4867427811407166926716741)
                ·
                  refine ⟨912642714638843798759389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4867427811407166926716741 912642714638843798759389)
                  ·
                    refine ⟨342241017989566424534771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912642714638843798759389 342241017989566424534771)
                    ·
                      rfl

theorem cell22_999768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_999768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999768 prefixEnd_999768 := by exact prefixLift 999768
  have htrace : WordTrace (prefixWord ++ tailWord_999768) baseStart_999768 baseEnd_999768 := by
    simpa [prefixWord, tailWord_999768, baseEnd_999768] using wordTrace_append hprefix tailTrace_999768
  have hstable : (prefixWord ++ tailWord_999768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999768).length < 2 ^ (prefixWord ++ tailWord_999768).sum := by decide
  have hdescent : baseEnd_999768 < baseStart_999768 := by decide
  rcases family_descends (prefixWord ++ tailWord_999768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999781 : List Nat := [1, 3, 1, 3, 1, 13]
def baseStart_999781 : Nat := 118140960795 + 999781 * 2 ^ 59
def prefixEnd_999781 : Nat := 4983230072969 + 3 ^ 40 * 999781 * 2
def baseEnd_999781 : Nat := 4225252693274552147651

theorem tailTrace_999781 : CollatzResearch.WordTrace tailWord_999781 prefixEnd_999781 4225252693274552147651 := by
  unfold tailWord_999781
  simp only [CollatzResearch.WordTrace]
  refine ⟨36465008790971660845887197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24310005860647773897258131 36465008790971660845887197)
  ·
    refine ⟨13674378296614372817207699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36465008790971660845887197 13674378296614372817207699)
    ·
      refine ⟨20511567444921559225811549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13674378296614372817207699 20511567444921559225811549)
      ·
        refine ⟨7691837791845584709679331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20511567444921559225811549 7691837791845584709679331)
        ·
          refine ⟨11537756687768377064518997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691837791845584709679331 11537756687768377064518997)
          ·
            refine ⟨4225252693274552147651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 11537756687768377064518997 4225252693274552147651)
            ·
              rfl

theorem cell22_999781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 13].length) (baseStart_999781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999781 prefixEnd_999781 := by exact prefixLift 999781
  have htrace : WordTrace (prefixWord ++ tailWord_999781) baseStart_999781 baseEnd_999781 := by
    simpa [prefixWord, tailWord_999781, baseEnd_999781] using wordTrace_append hprefix tailTrace_999781
  have hstable : (prefixWord ++ tailWord_999781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999781).length < 2 ^ (prefixWord ++ tailWord_999781).sum := by decide
  have hdescent : baseEnd_999781 < baseStart_999781 := by decide
  rcases family_descends (prefixWord ++ tailWord_999781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999785 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 2, 3]
def baseStart_999785 : Nat := 118140960795 + 999785 * 2 ^ 59
def prefixEnd_999785 : Nat := 4983230072969 + 3 ^ 40 * 999785 * 2
def baseEnd_999785 : Nat := 342246837436984046859719

theorem tailTrace_999785 : CollatzResearch.WordTrace tailWord_999785 prefixEnd_999785 342246837436984046859719 := by
  unfold tailWord_999785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36465154682957169529032809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24310103121971446352688539 36465154682957169529032809)
  ·
    refine ⟨27348866012217877146774607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36465154682957169529032809 27348866012217877146774607)
    ·
      refine ⟨41023299018326815720161911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27348866012217877146774607 41023299018326815720161911)
      ·
        refine ⟨61534948527490223580242867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41023299018326815720161911 61534948527490223580242867)
        ·
          refine ⟨92302422791235335370364301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61534948527490223580242867 92302422791235335370364301)
          ·
            refine ⟨34613408546713250763886613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92302422791235335370364301 34613408546713250763886613)
            ·
              refine ⟨1622503525627183629557185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34613408546713250763886613 1622503525627183629557185)
              ·
                refine ⟨1216877644220387722167889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622503525627183629557185 1216877644220387722167889)
                ·
                  refine ⟨912658233165290791625917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1216877644220387722167889 912658233165290791625917)
                  ·
                    refine ⟨342246837436984046859719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912658233165290791625917 342246837436984046859719)
                    ·
                      rfl

theorem cell22_999785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_999785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999785 prefixEnd_999785 := by exact prefixLift 999785
  have htrace : WordTrace (prefixWord ++ tailWord_999785) baseStart_999785 baseEnd_999785 := by
    simpa [prefixWord, tailWord_999785, baseEnd_999785] using wordTrace_append hprefix tailTrace_999785
  have hstable : (prefixWord ++ tailWord_999785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999785).length < 2 ^ (prefixWord ++ tailWord_999785).sum := by decide
  have hdescent : baseEnd_999785 < baseStart_999785 := by decide
  rcases family_descends (prefixWord ++ tailWord_999785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999843 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 7]
def baseStart_999843 : Nat := 118140960795 + 999843 * 2 ^ 59
def prefixEnd_999843 : Nat := 4983230072969 + 3 ^ 40 * 999843 * 2
def baseEnd_999843 : Nat := 114088897340763742969847

theorem tailTrace_999843 : CollatzResearch.WordTrace tailWord_999843 prefixEnd_999843 114088897340763742969847 := by
  unfold tailWord_999843
  simp only [CollatzResearch.WordTrace]
  refine ⟨36467270116747045434644183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24311513411164696956429455 36467270116747045434644183)
  ·
    refine ⟨54700905175120568151966275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36467270116747045434644183 54700905175120568151966275)
    ·
      refine ⟨82051357762680852227949413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54700905175120568151966275 82051357762680852227949413)
      ·
        refine ⟨15384629580502659792740515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82051357762680852227949413 15384629580502659792740515)
        ·
          refine ⟨23076944370753989689110773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384629580502659792740515 23076944370753989689110773)
          ·
            refine ⟨2163463534758186533354135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23076944370753989689110773 2163463534758186533354135)
            ·
              refine ⟨3245195302137279800031203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163463534758186533354135 3245195302137279800031203)
              ·
                refine ⟨4867792953205919700046805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245195302137279800031203 4867792953205919700046805)
                ·
                  refine ⟨114088897340763742969847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4867792953205919700046805 114088897340763742969847)
                  ·
                    rfl

theorem cell22_999843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 7].length) (baseStart_999843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999843 prefixEnd_999843 := by exact prefixLift 999843
  have htrace : WordTrace (prefixWord ++ tailWord_999843) baseStart_999843 baseEnd_999843 := by
    simpa [prefixWord, tailWord_999843, baseEnd_999843] using wordTrace_append hprefix tailTrace_999843
  have hstable : (prefixWord ++ tailWord_999843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999843).length < 2 ^ (prefixWord ++ tailWord_999843).sum := by decide
  have hdescent : baseEnd_999843 < baseStart_999843 := by decide
  rcases family_descends (prefixWord ++ tailWord_999843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999847 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 3, 3]
def baseStart_999847 : Nat := 118140960795 + 999847 * 2 ^ 59
def prefixEnd_999847 : Nat := 4983230072969 + 3 ^ 40 * 999847 * 2
def baseEnd_999847 : Nat := 342268061304036551809529

theorem tailTrace_999847 : CollatzResearch.WordTrace tailWord_999847 prefixEnd_999847 342268061304036551809529 := by
  unfold tailWord_999847
  simp only [CollatzResearch.WordTrace]
  refine ⟨36467416008732554117789795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24311610672488369411859863 36467416008732554117789795)
  ·
    refine ⟨54701124013098831176684693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36467416008732554117789795 54701124013098831176684693)
    ·
      refine ⟨2564115188114007711407095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54701124013098831176684693 2564115188114007711407095)
      ·
        refine ⟨3846172782171011567110643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564115188114007711407095 3846172782171011567110643)
        ·
          refine ⟨5769259173256517350665965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846172782171011567110643 5769259173256517350665965)
          ·
            refine ⟨2163472189971194006499737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5769259173256517350665965 2163472189971194006499737)
            ·
              refine ⟨1622604142478395504874803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163472189971194006499737 1622604142478395504874803)
              ·
                refine ⟨2433906213717593257312205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622604142478395504874803 2433906213717593257312205)
                ·
                  refine ⟨912714830144097471492077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2433906213717593257312205 912714830144097471492077)
                  ·
                    refine ⟨342268061304036551809529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912714830144097471492077 342268061304036551809529)
                    ·
                      rfl

theorem cell22_999847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_999847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999847 prefixEnd_999847 := by exact prefixLift 999847
  have htrace : WordTrace (prefixWord ++ tailWord_999847) baseStart_999847 baseEnd_999847 := by
    simpa [prefixWord, tailWord_999847, baseEnd_999847] using wordTrace_append hprefix tailTrace_999847
  have hstable : (prefixWord ++ tailWord_999847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999847).length < 2 ^ (prefixWord ++ tailWord_999847).sum := by decide
  have hdescent : baseEnd_999847 < baseStart_999847 := by decide
  rcases family_descends (prefixWord ++ tailWord_999847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999858 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_999858 : Nat := 118140960795 + 999858 * 2 ^ 59
def prefixEnd_999858 : Nat := 4983230072969 + 3 ^ 40 * 999858 * 2
def baseEnd_999858 : Nat := 342271826828836189784495

theorem tailTrace_999858 : CollatzResearch.WordTrace tailWord_999858 prefixEnd_999858 342271826828836189784495 := by
  unfold tailWord_999858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9116954302923175749110057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24311878141128468664293485 9116954302923175749110057)
  ·
    refine ⟨6837715727192381811832543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9116954302923175749110057 6837715727192381811832543)
    ·
      refine ⟨10256573590788572717748815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6837715727192381811832543 10256573590788572717748815)
      ·
        refine ⟨15384860386182859076623223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10256573590788572717748815 15384860386182859076623223)
        ·
          refine ⟨23077290579274288614934835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384860386182859076623223 23077290579274288614934835)
          ·
            refine ⟨34615935868911432922402253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23077290579274288614934835 34615935868911432922402253)
            ·
              refine ⟨12980975950841787345900845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34615935868911432922402253 12980975950841787345900845)
              ·
                refine ⟨4867865981565670254712817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12980975950841787345900845 4867865981565670254712817)
                ·
                  refine ⟨3650899486174252691034613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4867865981565670254712817 3650899486174252691034613)
                  ·
                    refine ⟨342271826828836189784495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3650899486174252691034613 342271826828836189784495)
                    ·
                      rfl

theorem cell22_999858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_999858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999858 prefixEnd_999858 := by exact prefixLift 999858
  have htrace : WordTrace (prefixWord ++ tailWord_999858) baseStart_999858 baseEnd_999858 := by
    simpa [prefixWord, tailWord_999858, baseEnd_999858] using wordTrace_append hprefix tailTrace_999858
  have hstable : (prefixWord ++ tailWord_999858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999858).length < 2 ^ (prefixWord ++ tailWord_999858).sum := by decide
  have hdescent : baseEnd_999858 < baseStart_999858 := by decide
  rcases family_descends (prefixWord ++ tailWord_999858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999933 : List Nat := [1, 4, 1, 1, 1, 3, 1, 10]
def baseStart_999933 : Nat := 118140960795 + 999933 * 2 ^ 59
def prefixEnd_999933 : Nat := 4983230072969 + 3 ^ 40 * 999933 * 2
def baseEnd_999933 : Nat := 38033055651284554906585

theorem tailTrace_999933 : CollatzResearch.WordTrace tailWord_999933 prefixEnd_999933 38033055651284554906585 := by
  unfold tailWord_999933
  simp only [CollatzResearch.WordTrace]
  refine ⟨36470552686420990805420453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24313701790947327203613635 36470552686420990805420453)
  ·
    refine ⟨6838228628703935776016335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36470552686420990805420453 6838228628703935776016335)
    ·
      refine ⟨10257342943055903664024503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6838228628703935776016335 10257342943055903664024503)
      ·
        refine ⟨15386014414583855496036755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10257342943055903664024503 15386014414583855496036755)
        ·
          refine ⟨23079021621875783244055133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15386014414583855496036755 23079021621875783244055133)
          ·
            refine ⟨8654633108203418716520675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23079021621875783244055133 8654633108203418716520675)
            ·
              refine ⟨12981949662305128074781013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8654633108203418716520675 12981949662305128074781013)
              ·
                refine ⟨38033055651284554906585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12981949662305128074781013 38033055651284554906585)
                ·
                  rfl

theorem cell22_999933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 10].length) (baseStart_999933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999933 prefixEnd_999933 := by exact prefixLift 999933
  have htrace : WordTrace (prefixWord ++ tailWord_999933) baseStart_999933 baseEnd_999933 := by
    simpa [prefixWord, tailWord_999933, baseEnd_999933] using wordTrace_append hprefix tailTrace_999933
  have hstable : (prefixWord ++ tailWord_999933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999933).length < 2 ^ (prefixWord ++ tailWord_999933).sum := by decide
  have hdescent : baseEnd_999933 < baseStart_999933 := by decide
  rcases family_descends (prefixWord ++ tailWord_999933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999935 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 2, 4]
def baseStart_999935 : Nat := 118140960795 + 999935 * 2 ^ 59
def prefixEnd_999935 : Nat := 4983230072969 + 3 ^ 40 * 999935 * 2
def baseEnd_999935 : Nat := 342298185502433655609259

theorem tailTrace_999935 : CollatzResearch.WordTrace tailWord_999935 prefixEnd_999935 342298185502433655609259 := by
  unfold tailWord_999935
  simp only [CollatzResearch.WordTrace]
  refine ⟨36470625632413745146993259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24313750421609163431328839 36470625632413745146993259)
  ·
    refine ⟨54705938448620617720489889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36470625632413745146993259 54705938448620617720489889)
    ·
      refine ⟨41029453836465463290367417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54705938448620617720489889 41029453836465463290367417)
      ·
        refine ⟨30772090377349097467775563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41029453836465463290367417 30772090377349097467775563)
        ·
          refine ⟨46158135566023646201663345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30772090377349097467775563 46158135566023646201663345)
          ·
            refine ⟨34618601674517734651247509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46158135566023646201663345 34618601674517734651247509)
            ·
              refine ⟨1622746953493018811777227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34618601674517734651247509 1622746953493018811777227)
              ·
                refine ⟨2434120430239528217665841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622746953493018811777227 2434120430239528217665841)
                ·
                  refine ⟨1825590322679646163249381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2434120430239528217665841 1825590322679646163249381)
                  ·
                    refine ⟨342298185502433655609259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1825590322679646163249381 342298185502433655609259)
                    ·
                      rfl

theorem cell22_999935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_999935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999935 prefixEnd_999935 := by exact prefixLift 999935
  have htrace : WordTrace (prefixWord ++ tailWord_999935) baseStart_999935 baseEnd_999935 := by
    simpa [prefixWord, tailWord_999935, baseEnd_999935] using wordTrace_append hprefix tailTrace_999935
  have hstable : (prefixWord ++ tailWord_999935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999935).length < 2 ^ (prefixWord ++ tailWord_999935).sum := by decide
  have hdescent : baseEnd_999935 < baseStart_999935 := by decide
  rcases family_descends (prefixWord ++ tailWord_999935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999956 : List Nat := [2, 4, 3, 1, 1, 1, 4, 2, 4]
def baseStart_999956 : Nat := 118140960795 + 999956 * 2 ^ 59
def prefixEnd_999956 : Nat := 4983230072969 + 3 ^ 40 * 999956 * 2
def baseEnd_999956 : Nat := 114101791410532200278065

theorem tailTrace_999956 : CollatzResearch.WordTrace tailWord_999956 prefixEnd_999956 114101791410532200278065 := by
  unfold tailWord_999956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18235695782668832866753861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24314261043558443822338481 18235695782668832866753861)
  ·
    refine ⟨3419192959250406162516349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18235695782668832866753861 3419192959250406162516349)
    ·
      refine ⟨1282197359718902310943631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3419192959250406162516349 1282197359718902310943631)
      ·
        refine ⟨1923296039578353466415447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282197359718902310943631 1923296039578353466415447)
        ·
          refine ⟨2884944059367530199623171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923296039578353466415447 2884944059367530199623171)
          ·
            refine ⟨4327416089051295299434757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884944059367530199623171 4327416089051295299434757)
            ·
              refine ⟨811390516697117868644017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4327416089051295299434757 811390516697117868644017)
              ·
                refine ⟨608542887522838401483013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811390516697117868644017 608542887522838401483013)
                ·
                  refine ⟨114101791410532200278065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608542887522838401483013 114101791410532200278065)
                  ·
                    rfl

theorem cell22_999956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_999956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999956 prefixEnd_999956 := by exact prefixLift 999956
  have htrace : WordTrace (prefixWord ++ tailWord_999956) baseStart_999956 baseEnd_999956 := by
    simpa [prefixWord, tailWord_999956, baseEnd_999956] using wordTrace_append hprefix tailTrace_999956
  have hstable : (prefixWord ++ tailWord_999956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999956).length < 2 ^ (prefixWord ++ tailWord_999956).sum := by decide
  have hdescent : baseEnd_999956 < baseStart_999956 := by decide
  rcases family_descends (prefixWord ++ tailWord_999956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999999 : List Nat := [1, 1, 2, 2, 3, 2, 4, 3, 1, 3]
def baseStart_999999 : Nat := 118140960795 + 999999 * 2 ^ 59
def prefixEnd_999999 : Nat := 4983230072969 + 3 ^ 40 * 999999 * 2
def baseEnd_999999 : Nat := 342320094010358822009063

theorem tailTrace_999999 : CollatzResearch.WordTrace tailWord_999999 prefixEnd_999999 342320094010358822009063 := by
  unfold tailWord_999999
  simp only [CollatzResearch.WordTrace]
  refine ⟨36472959904181884077323051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24315306602787922718215367 36472959904181884077323051)
  ·
    refine ⟨54709439856272826115984577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36472959904181884077323051 54709439856272826115984577)
    ·
      refine ⟨41032079892204619586988433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54709439856272826115984577 41032079892204619586988433)
      ·
        refine ⟨30774059919153464690241325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41032079892204619586988433 30774059919153464690241325)
        ·
          refine ⟨11540272469682549258840497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30774059919153464690241325 11540272469682549258840497)
          ·
            refine ⟨8655204352261911944130373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11540272469682549258840497 8655204352261911944130373)
            ·
              refine ⟨1622850816049108489524445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8655204352261911944130373 1622850816049108489524445)
              ·
                refine ⟨608569056018415683571667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1622850816049108489524445 608569056018415683571667)
                ·
                  refine ⟨912853584027623525357501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608569056018415683571667 912853584027623525357501)
                  ·
                    refine ⟨342320094010358822009063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912853584027623525357501 342320094010358822009063)
                    ·
                      rfl

theorem cell22_999999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 3].length) (baseStart_999999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_999999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_999999 prefixEnd_999999 := by exact prefixLift 999999
  have htrace : WordTrace (prefixWord ++ tailWord_999999) baseStart_999999 baseEnd_999999 := by
    simpa [prefixWord, tailWord_999999, baseEnd_999999] using wordTrace_append hprefix tailTrace_999999
  have hstable : (prefixWord ++ tailWord_999999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999999).length < 2 ^ (prefixWord ++ tailWord_999999).sum := by decide
  have hdescent : baseEnd_999999 < baseStart_999999 := by decide
  rcases family_descends (prefixWord ++ tailWord_999999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000010 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1000010 : Nat := 118140960795 + 1000010 * 2 ^ 59
def prefixEnd_1000010 : Nat := 4983230072969 + 3 ^ 40 * 1000010 * 2
def baseEnd_1000010 : Nat := 342323859535158459984029

theorem tailTrace_1000010 : CollatzResearch.WordTrace tailWord_1000010 prefixEnd_1000010 342323859535158459984029 := by
  unfold tailWord_1000010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9118340276785508238993371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24315574071428021970648989 9118340276785508238993371)
  ·
    refine ⟨13677510415178262358490057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9118340276785508238993371 13677510415178262358490057)
    ·
      refine ⟨10258132811383696768867543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13677510415178262358490057 10258132811383696768867543)
      ·
        refine ⟨15387199217075545153301315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10258132811383696768867543 15387199217075545153301315)
        ·
          refine ⟨23080798825613317729951973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15387199217075545153301315 23080798825613317729951973)
          ·
            refine ⟨4327649779802497074365995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23080798825613317729951973 4327649779802497074365995)
            ·
              refine ⟨6491474669703745611548993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327649779802497074365995 6491474669703745611548993)
              ·
                refine ⟨4868606002277809208661745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6491474669703745611548993 4868606002277809208661745)
                ·
                  refine ⟨3651454501708356906496309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4868606002277809208661745 3651454501708356906496309)
                  ·
                    refine ⟨342323859535158459984029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3651454501708356906496309 342323859535158459984029)
                    ·
                      rfl

theorem cell22_1000010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1000010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000010 prefixEnd_1000010 := by exact prefixLift 1000010
  have htrace : WordTrace (prefixWord ++ tailWord_1000010) baseStart_1000010 baseEnd_1000010 := by
    simpa [prefixWord, tailWord_1000010, baseEnd_1000010] using wordTrace_append hprefix tailTrace_1000010
  have hstable : (prefixWord ++ tailWord_1000010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000010).length < 2 ^ (prefixWord ++ tailWord_1000010).sum := by decide
  have hdescent : baseEnd_1000010 < baseStart_1000010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000055 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 1, 5]
def baseStart_1000055 : Nat := 118140960795 + 1000055 * 2 ^ 59
def prefixEnd_1000055 : Nat := 4983230072969 + 3 ^ 40 * 1000055 * 2
def baseEnd_1000055 : Nat := 342339263954793342608891

theorem tailTrace_1000055 : CollatzResearch.WordTrace tailWord_1000055 prefixEnd_1000055 342339263954793342608891 := by
  unfold tailWord_1000055
  simp only [CollatzResearch.WordTrace]
  refine ⟨36475002391979005641361619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24316668261319337094241079 36475002391979005641361619)
  ·
    refine ⟨54712503587968508462042429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36475002391979005641361619 54712503587968508462042429)
    ·
      refine ⟨20517188845488190673265911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54712503587968508462042429 20517188845488190673265911)
      ·
        refine ⟨30775783268232286009898867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20517188845488190673265911 30775783268232286009898867)
        ·
          refine ⟨46163674902348429014848301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30775783268232286009898867 46163674902348429014848301)
          ·
            refine ⟨17311378088380660880568113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46163674902348429014848301 17311378088380660880568113)
            ·
              refine ⟨12983533566285495660426085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17311378088380660880568113 12983533566285495660426085)
              ·
                refine ⟨2434412543678530436329891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12983533566285495660426085 2434412543678530436329891)
                ·
                  refine ⟨3651618815517795654494837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434412543678530436329891 3651618815517795654494837)
                  ·
                    refine ⟨342339263954793342608891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3651618815517795654494837 342339263954793342608891)
                    ·
                      rfl

theorem cell22_1000055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_1000055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000055 prefixEnd_1000055 := by exact prefixLift 1000055
  have htrace : WordTrace (prefixWord ++ tailWord_1000055) baseStart_1000055 baseEnd_1000055 := by
    simpa [prefixWord, tailWord_1000055, baseEnd_1000055] using wordTrace_append hprefix tailTrace_1000055
  have hstable : (prefixWord ++ tailWord_1000055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000055).length < 2 ^ (prefixWord ++ tailWord_1000055).sum := by decide
  have hdescent : baseEnd_1000055 < baseStart_1000055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000074 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_1000074 : Nat := 118140960795 + 1000074 * 2 ^ 59
def prefixEnd_1000074 : Nat := 4983230072969 + 3 ^ 40 * 1000074 * 2
def baseEnd_1000074 : Nat := 114115256014361208794611

theorem tailTrace_1000074 : CollatzResearch.WordTrace tailWord_1000074 prefixEnd_1000074 114115256014361208794611 := by
  unfold tailWord_1000074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9118923844727542971575819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24317130252606781257535517 9118923844727542971575819)
  ·
    refine ⟨13678385767091314457363729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9118923844727542971575819 13678385767091314457363729)
    ·
      refine ⟨10258789325318485843022797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13678385767091314457363729 10258789325318485843022797)
      ·
        refine ⟨3847045996994432191133549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10258789325318485843022797 3847045996994432191133549)
        ·
          refine ⟨1442642248872912071675081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3847045996994432191133549 1442642248872912071675081)
          ·
            refine ⟨1081981686654684053756311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1442642248872912071675081 1081981686654684053756311)
            ·
              refine ⟨1622972529982026080634467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081981686654684053756311 1622972529982026080634467)
              ·
                refine ⟨2434458794973039120951701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622972529982026080634467 2434458794973039120951701)
                ·
                  refine ⟨114115256014361208794611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2434458794973039120951701 114115256014361208794611)
                  ·
                    rfl

theorem cell22_1000074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_1000074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000074 prefixEnd_1000074 := by exact prefixLift 1000074
  have htrace : WordTrace (prefixWord ++ tailWord_1000074) baseStart_1000074 baseEnd_1000074 := by
    simpa [prefixWord, tailWord_1000074, baseEnd_1000074] using wordTrace_append hprefix tailTrace_1000074
  have hstable : (prefixWord ++ tailWord_1000074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000074).length < 2 ^ (prefixWord ++ tailWord_1000074).sum := by decide
  have hdescent : baseEnd_1000074 < baseStart_1000074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000106 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1000106 : Nat := 118140960795 + 1000106 * 2 ^ 59
def prefixEnd_1000106 : Nat := 4983230072969 + 3 ^ 40 * 1000106 * 2
def baseEnd_1000106 : Nat := 342356722297046209583735

theorem tailTrace_1000106 : CollatzResearch.WordTrace tailWord_1000106 prefixEnd_1000106 342356722297046209583735 := by
  unfold tailWord_1000106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119215628698560337867043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24317908343196160900978781 9119215628698560337867043)
  ·
    refine ⟨13678823443047840506800565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9119215628698560337867043 13678823443047840506800565)
    ·
      refine ⟨1282389697785735047512553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13678823443047840506800565 1282389697785735047512553)
      ·
        refine ⟨961792273339301285634415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1282389697785735047512553 961792273339301285634415)
        ·
          refine ⟨1442688410008951928451623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961792273339301285634415 1442688410008951928451623)
          ·
            refine ⟨2164032615013427892677435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442688410008951928451623 2164032615013427892677435)
            ·
              refine ⟨3246048922520141839016153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164032615013427892677435 3246048922520141839016153)
              ·
                refine ⟨2434536691890106379262115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246048922520141839016153 2434536691890106379262115)
                ·
                  refine ⟨3651805037835159568893173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434536691890106379262115 3651805037835159568893173)
                  ·
                    refine ⟨342356722297046209583735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3651805037835159568893173 342356722297046209583735)
                    ·
                      rfl

theorem cell22_1000106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1000106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000106 prefixEnd_1000106 := by exact prefixLift 1000106
  have htrace : WordTrace (prefixWord ++ tailWord_1000106) baseStart_1000106 baseEnd_1000106 := by
    simpa [prefixWord, tailWord_1000106, baseEnd_1000106] using wordTrace_append hprefix tailTrace_1000106
  have hstable : (prefixWord ++ tailWord_1000106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000106).length < 2 ^ (prefixWord ++ tailWord_1000106).sum := by decide
  have hdescent : baseEnd_1000106 < baseStart_1000106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000132 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1000132 : Nat := 118140960795 + 1000132 * 2 ^ 59
def prefixEnd_1000132 : Nat := 4983230072969 + 3 ^ 40 * 1000132 * 2
def baseEnd_1000132 : Nat := 342365622628390808433655

theorem tailTrace_1000132 : CollatzResearch.WordTrace tailWord_1000132 prefixEnd_1000132 342365622628390808433655 := by
  unfold tailWord_1000132
  simp only [CollatzResearch.WordTrace]
  refine ⟨18238905406350023895957325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24318540541800031861276433 18238905406350023895957325)
  ·
    refine ⟨6839589527381258960983997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18238905406350023895957325 6839589527381258960983997)
    ·
      refine ⟨2564846072767972110368999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6839589527381258960983997 2564846072767972110368999)
      ·
        refine ⟨3847269109151958165553499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564846072767972110368999 3847269109151958165553499)
        ·
          refine ⟨5770903663727937248330249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847269109151958165553499 5770903663727937248330249)
          ·
            refine ⟨4328177747795952936247687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5770903663727937248330249 4328177747795952936247687)
            ·
              refine ⟨6492266621693929404371531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328177747795952936247687 6492266621693929404371531)
              ·
                refine ⟨9738399932540894106557297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492266621693929404371531 9738399932540894106557297)
                ·
                  refine ⟨7303799949405670579917973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9738399932540894106557297 7303799949405670579917973)
                  ·
                    refine ⟨342365622628390808433655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7303799949405670579917973 342365622628390808433655)
                    ·
                      rfl

theorem cell22_1000132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1000132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000132 prefixEnd_1000132 := by exact prefixLift 1000132
  have htrace : WordTrace (prefixWord ++ tailWord_1000132) baseStart_1000132 baseEnd_1000132 := by
    simpa [prefixWord, tailWord_1000132, baseEnd_1000132] using wordTrace_append hprefix tailTrace_1000132
  have hstable : (prefixWord ++ tailWord_1000132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000132).length < 2 ^ (prefixWord ++ tailWord_1000132).sum := by decide
  have hdescent : baseEnd_1000132 < baseStart_1000132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000168 : List Nat := [2, 1, 4, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1000168 : Nat := 118140960795 + 1000168 * 2 ^ 59
def prefixEnd_1000168 : Nat := 4983230072969 + 3 ^ 40 * 1000168 * 2
def baseEnd_1000168 : Nat := 342377946164098714533545

theorem tailTrace_1000168 : CollatzResearch.WordTrace tailWord_1000168 prefixEnd_1000168 342377946164098714533545 := by
  unfold tailWord_1000168
  simp only [CollatzResearch.WordTrace]
  refine ⟨18239561920284812970112579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24319415893713083960150105 18239561920284812970112579)
  ·
    refine ⟨27359342880427219455168869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18239561920284812970112579 27359342880427219455168869)
    ·
      refine ⟨5129876790080103647844163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27359342880427219455168869 5129876790080103647844163)
      ·
        refine ⟨7694815185120155471766245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129876790080103647844163 7694815185120155471766245)
        ·
          refine ⟨1442777847210029150956171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7694815185120155471766245 1442777847210029150956171)
          ·
            refine ⟨2164166770815043726434257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442777847210029150956171 2164166770815043726434257)
            ·
              refine ⟨1623125078111282794825693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164166770815043726434257 1623125078111282794825693)
              ·
                refine ⟨608671904291731048059635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1623125078111282794825693 608671904291731048059635)
                ·
                  refine ⟨913007856437596572089453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608671904291731048059635 913007856437596572089453)
                  ·
                    refine ⟨342377946164098714533545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913007856437596572089453 342377946164098714533545)
                    ·
                      rfl

theorem cell22_1000168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1000168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000168 prefixEnd_1000168 := by exact prefixLift 1000168
  have htrace : WordTrace (prefixWord ++ tailWord_1000168) baseStart_1000168 baseEnd_1000168 := by
    simpa [prefixWord, tailWord_1000168, baseEnd_1000168] using wordTrace_append hprefix tailTrace_1000168
  have hstable : (prefixWord ++ tailWord_1000168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000168).length < 2 ^ (prefixWord ++ tailWord_1000168).sum := by decide
  have hdescent : baseEnd_1000168 < baseStart_1000168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000224 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 4, 3]
def baseStart_1000224 : Nat := 118140960795 + 1000224 * 2 ^ 59
def prefixEnd_1000224 : Nat := 4983230072969 + 3 ^ 40 * 1000224 * 2
def baseEnd_1000224 : Nat := 342397116108533235133373

theorem tailTrace_1000224 : CollatzResearch.WordTrace tailWord_1000224 prefixEnd_1000224 342397116108533235133373 := by
  unfold tailWord_1000224
  simp only [CollatzResearch.WordTrace]
  refine ⟨18240583164183373752131863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24320777552244498336175817 18240583164183373752131863)
  ·
    refine ⟨27360874746275060628197795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18240583164183373752131863 27360874746275060628197795)
    ·
      refine ⟨41041312119412590942296693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27360874746275060628197795 41041312119412590942296693)
      ·
        refine ⟨3847623011194930400840315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41041312119412590942296693 3847623011194930400840315)
        ·
          refine ⟨5771434516792395601260473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847623011194930400840315 5771434516792395601260473)
          ·
            refine ⟨4328575887594296700945355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5771434516792395601260473 4328575887594296700945355)
            ·
              refine ⟨6492863831391445051418033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328575887594296700945355 6492863831391445051418033)
              ·
                refine ⟨4869647873543583788563525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6492863831391445051418033 4869647873543583788563525)
                ·
                  refine ⟨913058976289421960355661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4869647873543583788563525 913058976289421960355661)
                  ·
                    refine ⟨342397116108533235133373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913058976289421960355661 342397116108533235133373)
                    ·
                      rfl

theorem cell22_1000224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_1000224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000224 prefixEnd_1000224 := by exact prefixLift 1000224
  have htrace : WordTrace (prefixWord ++ tailWord_1000224) baseStart_1000224 baseEnd_1000224 := by
    simpa [prefixWord, tailWord_1000224, baseEnd_1000224] using wordTrace_append hprefix tailTrace_1000224
  have hstable : (prefixWord ++ tailWord_1000224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000224).length < 2 ^ (prefixWord ++ tailWord_1000224).sum := by decide
  have hdescent : baseEnd_1000224 < baseStart_1000224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000226 : List Nat := [3, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1000226 : Nat := 118140960795 + 1000226 * 2 ^ 59
def prefixEnd_1000226 : Nat := 4983230072969 + 3 ^ 40 * 1000226 * 2
def baseEnd_1000226 : Nat := 114132600249801965527789

theorem tailTrace_1000226 : CollatzResearch.WordTrace tailWord_1000226 prefixEnd_1000226 114132600249801965527789 := by
  unfold tailWord_1000226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120309818589875461459133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24320826182906334563891021 9120309818589875461459133)
  ·
    refine ⟨3420116181971203298047175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9120309818589875461459133 3420116181971203298047175)
    ·
      refine ⟨5130174272956804947070763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420116181971203298047175 5130174272956804947070763)
      ·
        refine ⟨7695261409435207420606145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130174272956804947070763 7695261409435207420606145)
        ·
          refine ⟨5771446057076405565454609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7695261409435207420606145 5771446057076405565454609)
          ·
            refine ⟨4328584542807304174090957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5771446057076405565454609 4328584542807304174090957)
            ·
              refine ⟨1623219203552739065284109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4328584542807304174090957 1623219203552739065284109)
              ·
                refine ⟨608707201332277149481541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1623219203552739065284109 608707201332277149481541)
                ·
                  refine ⟨114132600249801965527789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608707201332277149481541 114132600249801965527789)
                  ·
                    rfl

theorem cell22_1000226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1000226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000226 prefixEnd_1000226 := by exact prefixLift 1000226
  have htrace : WordTrace (prefixWord ++ tailWord_1000226) baseStart_1000226 baseEnd_1000226 := by
    simpa [prefixWord, tailWord_1000226, baseEnd_1000226] using wordTrace_append hprefix tailTrace_1000226
  have hstable : (prefixWord ++ tailWord_1000226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000226).length < 2 ^ (prefixWord ++ tailWord_1000226).sum := by decide
  have hdescent : baseEnd_1000226 < baseStart_1000226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000262 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1000262 : Nat := 118140960795 + 1000262 * 2 ^ 59
def prefixEnd_1000262 : Nat := 4983230072969 + 3 ^ 40 * 1000262 * 2
def baseEnd_1000262 : Nat := 342410124285113802683257

theorem tailTrace_1000262 : CollatzResearch.WordTrace tailWord_1000262 prefixEnd_1000262 342410124285113802683257 := by
  unfold tailWord_1000262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140079759444658749817095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24321701534819386662764693 1140079759444658749817095)
  ·
    refine ⟨1710119639166988124725643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1140079759444658749817095 1710119639166988124725643)
    ·
      refine ⟨2565179458750482187088465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710119639166988124725643 2565179458750482187088465)
      ·
        refine ⟨1923884594062861640316349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2565179458750482187088465 1923884594062861640316349)
        ·
          refine ⟨721456722773573115118631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1923884594062861640316349 721456722773573115118631)
          ·
            refine ⟨1082185084160359672677947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721456722773573115118631 1082185084160359672677947)
            ·
              refine ⟨1623277626240539509016921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082185084160359672677947 1623277626240539509016921)
              ·
                refine ⟨1217458219680404631762691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623277626240539509016921 1217458219680404631762691)
                ·
                  refine ⟨1826187329520606947644037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217458219680404631762691 1826187329520606947644037)
                  ·
                    refine ⟨342410124285113802683257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1826187329520606947644037 342410124285113802683257)
                    ·
                      rfl

theorem cell22_1000262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1000262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000262 prefixEnd_1000262 := by exact prefixLift 1000262
  have htrace : WordTrace (prefixWord ++ tailWord_1000262) baseStart_1000262 baseEnd_1000262 := by
    simpa [prefixWord, tailWord_1000262, baseEnd_1000262] using wordTrace_append hprefix tailTrace_1000262
  have hstable : (prefixWord ++ tailWord_1000262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000262).length < 2 ^ (prefixWord ++ tailWord_1000262).sum := by decide
  have hdescent : baseEnd_1000262 < baseStart_1000262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000329 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_1000329 : Nat := 118140960795 + 1000329 * 2 ^ 59
def prefixEnd_1000329 : Nat := 4983230072969 + 3 ^ 40 * 1000329 * 2
def baseEnd_1000329 : Nat := 342433059754347961258051

theorem tailTrace_1000329 : CollatzResearch.WordTrace tailWord_1000329 prefixEnd_1000329 342433059754347961258051 := by
  unfold tailWord_1000329
  simp only [CollatzResearch.WordTrace]
  refine ⟨36484995992986350436836041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24323330661990900291224027 36484995992986350436836041)
  ·
    refine ⟨27363746994739762827627031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36484995992986350436836041 27363746994739762827627031)
    ·
      refine ⟨41045620492109644241440547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27363746994739762827627031 41045620492109644241440547)
      ·
        refine ⟨61568430738164466362160821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41045620492109644241440547 61568430738164466362160821)
        ·
          refine ⟨5772040381702918721452577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61568430738164466362160821 5772040381702918721452577)
          ·
            refine ⟨4329030286277189041089433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5772040381702918721452577 4329030286277189041089433)
            ·
              refine ⟨3246772714707891780817075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4329030286277189041089433 3246772714707891780817075)
              ·
                refine ⟨4870159072061837671225613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246772714707891780817075 4870159072061837671225613)
                ·
                  refine ⟨1826309652023189126709605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4870159072061837671225613 1826309652023189126709605)
                  ·
                    refine ⟨342433059754347961258051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1826309652023189126709605 342433059754347961258051)
                    ·
                      rfl

theorem cell22_1000329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_1000329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000329 prefixEnd_1000329 := by exact prefixLift 1000329
  have htrace : WordTrace (prefixWord ++ tailWord_1000329) baseStart_1000329 baseEnd_1000329 := by
    simpa [prefixWord, tailWord_1000329, baseEnd_1000329] using wordTrace_append hprefix tailTrace_1000329
  have hstable : (prefixWord ++ tailWord_1000329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000329).length < 2 ^ (prefixWord ++ tailWord_1000329).sum := by decide
  have hdescent : baseEnd_1000329 < baseStart_1000329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000376 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 1, 5]
def baseStart_1000376 : Nat := 118140960795 + 1000376 * 2 ^ 59
def prefixEnd_1000376 : Nat := 4983230072969 + 3 ^ 40 * 1000376 * 2
def baseEnd_1000376 : Nat := 342449148814855505332907

theorem tailTrace_1000376 : CollatzResearch.WordTrace tailWord_1000376 prefixEnd_1000376 342449148814855505332907 := by
  unfold tailWord_1000376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18243355111908038731898491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24324473482544051642531321 18243355111908038731898491)
  ·
    refine ⟨27365032667862058097847737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18243355111908038731898491 27365032667862058097847737)
    ·
      refine ⟨20523774500896543573385803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27365032667862058097847737 20523774500896543573385803)
      ·
        refine ⟨30785661751344815360078705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20523774500896543573385803 30785661751344815360078705)
        ·
          refine ⟨23089246313508611520059029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30785661751344815360078705 23089246313508611520059029)
          ·
            refine ⟨1082308420945716165002767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23089246313508611520059029 1082308420945716165002767)
            ·
              refine ⟨1623462631418574247504151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082308420945716165002767 1623462631418574247504151)
              ·
                refine ⟨2435193947127861371256227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623462631418574247504151 2435193947127861371256227)
                ·
                  refine ⟨3652790920691792056884341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435193947127861371256227 3652790920691792056884341)
                  ·
                    refine ⟨342449148814855505332907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3652790920691792056884341 342449148814855505332907)
                    ·
                      rfl

theorem cell22_1000376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_1000376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000376 prefixEnd_1000376 := by exact prefixLift 1000376
  have htrace : WordTrace (prefixWord ++ tailWord_1000376) baseStart_1000376 baseEnd_1000376 := by
    simpa [prefixWord, tailWord_1000376, baseEnd_1000376] using wordTrace_append hprefix tailTrace_1000376
  have hstable : (prefixWord ++ tailWord_1000376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000376).length < 2 ^ (prefixWord ++ tailWord_1000376).sum := by decide
  have hdescent : baseEnd_1000376 < baseStart_1000376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000406 : List Nat := [5, 2, 1, 1, 2, 1, 10]
def baseStart_1000406 : Nat := 118140960795 + 1000406 * 2 ^ 59
def prefixEnd_1000406 : Nat := 4983230072969 + 3 ^ 40 * 1000406 * 2
def baseEnd_1000406 : Nat := 12683682163997978780845

theorem tailTrace_1000406 : CollatzResearch.WordTrace tailWord_1000406 prefixEnd_1000406 12683682163997978780845 := by
  unfold tailWord_1000406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280487775856712036711817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24325202942471595058259381 2280487775856712036711817)
  ·
    refine ⟨1710365831892534027533863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2280487775856712036711817 1710365831892534027533863)
    ·
      refine ⟨2565548747838801041300795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710365831892534027533863 2565548747838801041300795)
      ·
        refine ⟨3848323121758201561951193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565548747838801041300795 3848323121758201561951193)
        ·
          refine ⟨2886242341318651171463395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3848323121758201561951193 2886242341318651171463395)
          ·
            refine ⟨4329363511977976757195093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886242341318651171463395 4329363511977976757195093)
            ·
              refine ⟨12683682163997978780845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4329363511977976757195093 12683682163997978780845)
              ·
                rfl

theorem cell22_1000406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 10].length) (baseStart_1000406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000406 prefixEnd_1000406 := by exact prefixLift 1000406
  have htrace : WordTrace (prefixWord ++ tailWord_1000406) baseStart_1000406 baseEnd_1000406 := by
    simpa [prefixWord, tailWord_1000406, baseEnd_1000406] using wordTrace_append hprefix tailTrace_1000406
  have hstable : (prefixWord ++ tailWord_1000406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000406).length < 2 ^ (prefixWord ++ tailWord_1000406).sum := by decide
  have hdescent : baseEnd_1000406 < baseStart_1000406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000419 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 2, 6]
def baseStart_1000419 : Nat := 118140960795 + 1000419 * 2 ^ 59
def prefixEnd_1000419 : Nat := 4983230072969 + 3 ^ 40 * 1000419 * 2
def baseEnd_1000419 : Nat := 342463868593617726507775

theorem tailTrace_1000419 : CollatzResearch.WordTrace tailWord_1000419 prefixEnd_1000419 342463868593617726507775 := by
  unfold tailWord_1000419
  simp only [CollatzResearch.WordTrace]
  refine ⟨36488278562660295807612311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24325519041773530538408207 36488278562660295807612311)
  ·
    refine ⟨54732417843990443711418467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36488278562660295807612311 54732417843990443711418467)
    ·
      refine ⟨82098626765985665567127701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54732417843990443711418467 82098626765985665567127701)
      ·
        refine ⟨3848373129655578073459111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82098626765985665567127701 3848373129655578073459111)
        ·
          refine ⟨5772559694483367110188667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848373129655578073459111 5772559694483367110188667)
          ·
            refine ⟨8658839541725050665283001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772559694483367110188667 8658839541725050665283001)
            ·
              refine ⟨6494129656293787998962251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8658839541725050665283001 6494129656293787998962251)
              ·
                refine ⟨9741194484440681998443377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494129656293787998962251 9741194484440681998443377)
                ·
                  refine ⟨7305895863330511498832533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9741194484440681998443377 7305895863330511498832533)
                  ·
                    refine ⟨342463868593617726507775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7305895863330511498832533 342463868593617726507775)
                    ·
                      rfl

theorem cell22_1000419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_1000419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000419 prefixEnd_1000419 := by exact prefixLift 1000419
  have htrace : WordTrace (prefixWord ++ tailWord_1000419) baseStart_1000419 baseEnd_1000419 := by
    simpa [prefixWord, tailWord_1000419, baseEnd_1000419] using wordTrace_append hprefix tailTrace_1000419
  have hstable : (prefixWord ++ tailWord_1000419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000419).length < 2 ^ (prefixWord ++ tailWord_1000419).sum := by decide
  have hdescent : baseEnd_1000419 < baseStart_1000419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000464 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_1000464 : Nat := 118140960795 + 1000464 * 2 ^ 59
def prefixEnd_1000464 : Nat := 4983230072969 + 3 ^ 40 * 1000464 * 2
def baseEnd_1000464 : Nat := 342479273013252609132637

theorem tailTrace_1000464 : CollatzResearch.WordTrace tailWord_1000464 prefixEnd_1000464 342479273013252609132637 := by
  unfold tailWord_1000464
  simp only [CollatzResearch.WordTrace]
  refine ⟨18244959923748634246500223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24326613231664845662000297 18244959923748634246500223)
  ·
    refine ⟨27367439885622951369750335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18244959923748634246500223 27367439885622951369750335)
    ·
      refine ⟨41051159828434427054625503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27367439885622951369750335 41051159828434427054625503)
      ·
        refine ⟨61576739742651640581938255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41051159828434427054625503 61576739742651640581938255)
        ·
          refine ⟨92365109613977460872907383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61576739742651640581938255 92365109613977460872907383)
          ·
            refine ⟨138547664420966191309361075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92365109613977460872907383 138547664420966191309361075)
            ·
              refine ⟨207821496631449286964041613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138547664420966191309361075 207821496631449286964041613)
              ·
                refine ⟨77933061236793482611515605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207821496631449286964041613 77933061236793482611515605)
                ·
                  refine ⟨1826556122737347248707397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 77933061236793482611515605 1826556122737347248707397)
                  ·
                    refine ⟨342479273013252609132637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1826556122737347248707397 342479273013252609132637)
                    ·
                      rfl

theorem cell22_1000464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_1000464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000464 prefixEnd_1000464 := by exact prefixLift 1000464
  have htrace : WordTrace (prefixWord ++ tailWord_1000464) baseStart_1000464 baseEnd_1000464 := by
    simpa [prefixWord, tailWord_1000464, baseEnd_1000464] using wordTrace_append hprefix tailTrace_1000464
  have hstable : (prefixWord ++ tailWord_1000464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000464).length < 2 ^ (prefixWord ++ tailWord_1000464).sum := by decide
  have hdescent : baseEnd_1000464 < baseStart_1000464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000472 : List Nat := [2, 1, 2, 3, 2, 4, 2, 2, 1, 3]
def baseStart_1000472 : Nat := 118140960795 + 1000472 * 2 ^ 59
def prefixEnd_1000472 : Nat := 4983230072969 + 3 ^ 40 * 1000472 * 2
def baseEnd_1000472 : Nat := 342482011576743254932613

theorem tailTrace_1000472 : CollatzResearch.WordTrace tailWord_1000472 prefixEnd_1000472 342482011576743254932613 := by
  unfold tailWord_1000472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245105815734142929645835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24326807754312190572861113 18245105815734142929645835)
  ·
    refine ⟨27367658723601214394468753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18245105815734142929645835 27367658723601214394468753)
    ·
      refine ⟨20525744042700910795851565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27367658723601214394468753 20525744042700910795851565)
      ·
        refine ⟨7697154016012841548444337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20525744042700910795851565 7697154016012841548444337)
        ·
          refine ⟨5772865512009631161333253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697154016012841548444337 5772865512009631161333253)
          ·
            refine ⟨1082412283501805842749985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5772865512009631161333253 1082412283501805842749985)
            ·
              refine ⟨811809212626354382062489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082412283501805842749985 811809212626354382062489)
              ·
                refine ⟨608856909469765786546867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811809212626354382062489 608856909469765786546867)
                ·
                  refine ⟨913285364204648679820301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608856909469765786546867 913285364204648679820301)
                  ·
                    refine ⟨342482011576743254932613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913285364204648679820301 342482011576743254932613)
                    ·
                      rfl

theorem cell22_1000472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_1000472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000472 prefixEnd_1000472 := by exact prefixLift 1000472
  have htrace : WordTrace (prefixWord ++ tailWord_1000472) baseStart_1000472 baseEnd_1000472 := by
    simpa [prefixWord, tailWord_1000472, baseEnd_1000472] using wordTrace_append hprefix tailTrace_1000472
  have hstable : (prefixWord ++ tailWord_1000472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000472).length < 2 ^ (prefixWord ++ tailWord_1000472).sum := by decide
  have hdescent : baseEnd_1000472 < baseStart_1000472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000481 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1000481 : Nat := 118140960795 + 1000481 * 2 ^ 59
def prefixEnd_1000481 : Nat := 4983230072969 + 3 ^ 40 * 1000481 * 2
def baseEnd_1000481 : Nat := 342485092460670231457585

theorem tailTrace_1000481 : CollatzResearch.WordTrace tailWord_1000481 prefixEnd_1000481 342485092460670231457585 := by
  unfold tailWord_1000481
  simp only [CollatzResearch.WordTrace]
  refine ⟨36490539888435680396369297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24327026592290453597579531 36490539888435680396369297)
  ·
    refine ⟨27367904916326760297276973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36490539888435680396369297 27367904916326760297276973)
    ·
      refine ⟨10262964343622535111478865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27367904916326760297276973 10262964343622535111478865)
      ·
        refine ⟨7697223257716901333609149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10262964343622535111478865 7697223257716901333609149)
        ·
          refine ⟨2886458721643838000103431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7697223257716901333609149 2886458721643838000103431)
          ·
            refine ⟨4329688082465757000155147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886458721643838000103431 4329688082465757000155147)
            ·
              refine ⟨6494532123698635500232721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329688082465757000155147 6494532123698635500232721)
              ·
                refine ⟨4870899092773976625174541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6494532123698635500232721 4870899092773976625174541)
                ·
                  refine ⟨1826587159790241234440453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4870899092773976625174541 1826587159790241234440453)
                  ·
                    refine ⟨342485092460670231457585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1826587159790241234440453 342485092460670231457585)
                    ·
                      rfl

theorem cell22_1000481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1000481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000481 prefixEnd_1000481 := by exact prefixLift 1000481
  have htrace : WordTrace (prefixWord ++ tailWord_1000481) baseStart_1000481 baseEnd_1000481 := by
    simpa [prefixWord, tailWord_1000481, baseEnd_1000481] using wordTrace_append hprefix tailTrace_1000481
  have hstable : (prefixWord ++ tailWord_1000481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000481).length < 2 ^ (prefixWord ++ tailWord_1000481).sum := by decide
  have hdescent : baseEnd_1000481 < baseStart_1000481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000511 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 4, 3]
def baseStart_1000511 : Nat := 118140960795 + 1000511 * 2 ^ 59
def prefixEnd_1000511 : Nat := 4983230072969 + 3 ^ 40 * 1000511 * 2
def baseEnd_1000511 : Nat := 342495362073760153207493

theorem tailTrace_1000511 : CollatzResearch.WordTrace tailWord_1000511 prefixEnd_1000511 342495362073760153207493 := by
  unfold tailWord_1000511
  simp only [CollatzResearch.WordTrace]
  refine ⟨36491634078326995519961387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24327756052217997013307591 36491634078326995519961387)
  ·
    refine ⟨54737451117490493279942081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36491634078326995519961387 54737451117490493279942081)
    ·
      refine ⟨41053088338117869959956561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54737451117490493279942081 41053088338117869959956561)
      ·
        refine ⟨30789816253588402469967421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41053088338117869959956561 30789816253588402469967421)
        ·
          refine ⟨11546181095095650926237783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30789816253588402469967421 11546181095095650926237783)
          ·
            refine ⟨17319271642643476389356675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11546181095095650926237783 17319271642643476389356675)
            ·
              refine ⟨25978907463965214584035013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17319271642643476389356675 25978907463965214584035013)
              ·
                refine ⟨4871045149493477734506565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25978907463965214584035013 4871045149493477734506565)
                ·
                  refine ⟨913320965530027075219981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4871045149493477734506565 913320965530027075219981)
                  ·
                    refine ⟨342495362073760153207493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913320965530027075219981 342495362073760153207493)
                    ·
                      rfl

theorem cell22_1000511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_1000511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000511 prefixEnd_1000511 := by exact prefixLift 1000511
  have htrace : WordTrace (prefixWord ++ tailWord_1000511) baseStart_1000511 baseEnd_1000511 := by
    simpa [prefixWord, tailWord_1000511, baseEnd_1000511] using wordTrace_append hprefix tailTrace_1000511
  have hstable : (prefixWord ++ tailWord_1000511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000511).length < 2 ^ (prefixWord ++ tailWord_1000511).sum := by decide
  have hdescent : baseEnd_1000511 < baseStart_1000511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000526 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1000526 : Nat := 118140960795 + 1000526 * 2 ^ 59
def prefixEnd_1000526 : Nat := 4983230072969 + 3 ^ 40 * 1000526 * 2
def baseEnd_1000526 : Nat := 342500496880305114082447

theorem tailTrace_1000526 : CollatzResearch.WordTrace tailWord_1000526 prefixEnd_1000526 342500496880305114082447 := by
  unfold tailWord_1000526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561522646659081635219679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24328120782181768721171621 4561522646659081635219679)
  ·
    refine ⟨6842283969988622452829519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561522646659081635219679 6842283969988622452829519)
    ·
      refine ⟨10263425954982933679244279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6842283969988622452829519 10263425954982933679244279)
      ·
        refine ⟨15395138932474400518866419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10263425954982933679244279 15395138932474400518866419)
        ·
          refine ⟨23092708398711600778299629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15395138932474400518866419 23092708398711600778299629)
          ·
            refine ⟨8659765649516850291862361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23092708398711600778299629 8659765649516850291862361)
            ·
              refine ⟨6494824237137637718896771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8659765649516850291862361 6494824237137637718896771)
              ·
                refine ⟨9742236355706456578345157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494824237137637718896771 9742236355706456578345157)
                ·
                  refine ⟨1826669316694960608439717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9742236355706456578345157 1826669316694960608439717)
                  ·
                    refine ⟨342500496880305114082447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1826669316694960608439717 342500496880305114082447)
                    ·
                      rfl

theorem cell22_1000526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1000526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000526 prefixEnd_1000526 := by exact prefixLift 1000526
  have htrace : WordTrace (prefixWord ++ tailWord_1000526) baseStart_1000526 baseEnd_1000526 := by
    simpa [prefixWord, tailWord_1000526, baseEnd_1000526] using wordTrace_append hprefix tailTrace_1000526
  have hstable : (prefixWord ++ tailWord_1000526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000526).length < 2 ^ (prefixWord ++ tailWord_1000526).sum := by decide
  have hdescent : baseEnd_1000526 < baseStart_1000526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000558 : List Nat := [4, 1, 2, 2, 1, 2, 4, 6]
def baseStart_1000558 : Nat := 118140960795 + 1000558 * 2 ^ 59
def prefixEnd_1000558 : Nat := 4983230072969 + 3 ^ 40 * 1000558 * 2
def baseEnd_1000558 : Nat := 38056827903807521920261

theorem tailTrace_1000558 : CollatzResearch.WordTrace tailWord_1000558 prefixEnd_1000558 38056827903807521920261 := by
  unfold tailWord_1000558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561668538644590318365291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24328898872771148364614885 4561668538644590318365291)
  ·
    refine ⟨6842502807966885477547937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561668538644590318365291 6842502807966885477547937)
    ·
      refine ⟨5131877105975164108160953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6842502807966885477547937 5131877105975164108160953)
      ·
        refine ⟨3848907829481373081120715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5131877105975164108160953 3848907829481373081120715)
        ·
          refine ⟨5773361744222059621681073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848907829481373081120715 5773361744222059621681073)
          ·
            refine ⟨4330021308166544716260805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773361744222059621681073 4330021308166544716260805)
            ·
              refine ⟨811878995281227134298901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4330021308166544716260805 811878995281227134298901)
              ·
                refine ⟨38056827903807521920261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 811878995281227134298901 38056827903807521920261)
                ·
                  rfl

theorem cell22_1000558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_1000558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000558 prefixEnd_1000558 := by exact prefixLift 1000558
  have htrace : WordTrace (prefixWord ++ tailWord_1000558) baseStart_1000558 baseEnd_1000558 := by
    simpa [prefixWord, tailWord_1000558, baseEnd_1000558] using wordTrace_append hprefix tailTrace_1000558
  have hstable : (prefixWord ++ tailWord_1000558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000558).length < 2 ^ (prefixWord ++ tailWord_1000558).sum := by decide
  have hdescent : baseEnd_1000558 < baseStart_1000558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000586 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_1000586 : Nat := 118140960795 + 1000586 * 2 ^ 59
def prefixEnd_1000586 : Nat := 4983230072969 + 3 ^ 40 * 1000586 * 2
def baseEnd_1000586 : Nat := 114173678702161652527421

theorem tailTrace_1000586 : CollatzResearch.WordTrace tailWord_1000586 prefixEnd_1000586 114173678702161652527421 := by
  unfold tailWord_1000586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9123592388263820832235403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24329579702036855552627741 9123592388263820832235403)
  ·
    refine ⟨13685388582395731248353105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9123592388263820832235403 13685388582395731248353105)
    ·
      refine ⟨10264041436796798436264829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13685388582395731248353105 10264041436796798436264829)
      ·
        refine ⟨3849015538798799413599311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10264041436796798436264829 3849015538798799413599311)
        ·
          refine ⟨5773523308198199120398967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849015538798799413599311 5773523308198199120398967)
          ·
            refine ⟨8660284962297298680598451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773523308198199120398967 8660284962297298680598451)
            ·
              refine ⟨12990427443445948020897677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8660284962297298680598451 12990427443445948020897677)
              ·
                refine ⟨4871410291292230507836629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12990427443445948020897677 4871410291292230507836629)
                ·
                  refine ⟨114173678702161652527421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4871410291292230507836629 114173678702161652527421)
                  ·
                    rfl

theorem cell22_1000586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_1000586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000586 prefixEnd_1000586 := by exact prefixLift 1000586
  have htrace : WordTrace (prefixWord ++ tailWord_1000586) baseStart_1000586 baseEnd_1000586 := by
    simpa [prefixWord, tailWord_1000586, baseEnd_1000586] using wordTrace_append hprefix tailTrace_1000586
  have hstable : (prefixWord ++ tailWord_1000586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000586).length < 2 ^ (prefixWord ++ tailWord_1000586).sum := by decide
  have hdescent : baseEnd_1000586 < baseStart_1000586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000590 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_1000590 : Nat := 118140960795 + 1000590 * 2 ^ 59
def prefixEnd_1000590 : Nat := 4983230072969 + 3 ^ 40 * 1000590 * 2
def baseEnd_1000590 : Nat := 342522405388230280482251

theorem tailTrace_1000590 : CollatzResearch.WordTrace tailWord_1000590 prefixEnd_1000590 342522405388230280482251 := by
  unfold tailWord_1000590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561814430630099001510903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24329676963360528008058149 4561814430630099001510903)
  ·
    refine ⟨6842721645945148502266355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561814430630099001510903 6842721645945148502266355)
    ·
      refine ⟨10264082468917722753399533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6842721645945148502266355 10264082468917722753399533)
      ·
        refine ⟨3849030925844146032524825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10264082468917722753399533 3849030925844146032524825)
        ·
          refine ⟨2886773194383109524393619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3849030925844146032524825 2886773194383109524393619)
          ·
            refine ⟨4330159791574664286590429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886773194383109524393619 4330159791574664286590429)
            ·
              refine ⟨1623809921840499107471411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4330159791574664286590429 1623809921840499107471411)
              ·
                refine ⟨2435714882760748661207117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623809921840499107471411 2435714882760748661207117)
                ·
                  refine ⟨913393081035280747952669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2435714882760748661207117 913393081035280747952669)
                  ·
                    refine ⟨342522405388230280482251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913393081035280747952669 342522405388230280482251)
                    ·
                      rfl

theorem cell22_1000590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_1000590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000590 prefixEnd_1000590 := by exact prefixLift 1000590
  have htrace : WordTrace (prefixWord ++ tailWord_1000590) baseStart_1000590 baseEnd_1000590 := by
    simpa [prefixWord, tailWord_1000590, baseEnd_1000590] using wordTrace_append hprefix tailTrace_1000590
  have hstable : (prefixWord ++ tailWord_1000590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000590).length < 2 ^ (prefixWord ++ tailWord_1000590).sum := by decide
  have hdescent : baseEnd_1000590 < baseStart_1000590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000641 : List Nat := [1, 2, 6, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1000641 : Nat := 118140960795 + 1000641 * 2 ^ 59
def prefixEnd_1000641 : Nat := 4983230072969 + 3 ^ 40 * 1000641 * 2
def baseEnd_1000641 : Nat := 342539863730483147457095

theorem tailTrace_1000641 : CollatzResearch.WordTrace tailWord_1000641 prefixEnd_1000641 342539863730483147457095 := by
  unfold tailWord_1000641
  simp only [CollatzResearch.WordTrace]
  refine ⟨36496375567856027722193777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24330917045237351814795851 36496375567856027722193777)
  ·
    refine ⟨27372281675892020791645333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36496375567856027722193777 27372281675892020791645333)
    ·
      refine ⟨1283075703557438474608375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27372281675892020791645333 1283075703557438474608375)
      ·
        refine ⟨1924613555336157711912563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283075703557438474608375 1924613555336157711912563)
        ·
          refine ⟨2886920333004236567868845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924613555336157711912563 2886920333004236567868845)
          ·
            refine ⟨1082595124876588712950817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2886920333004236567868845 1082595124876588712950817)
            ·
              refine ⟨811946343657441534713113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082595124876588712950817 811946343657441534713113)
              ·
                refine ⟨608959757743081151034835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811946343657441534713113 608959757743081151034835)
                ·
                  refine ⟨913439636614621726552253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608959757743081151034835 913439636614621726552253)
                  ·
                    refine ⟨342539863730483147457095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913439636614621726552253 342539863730483147457095)
                    ·
                      rfl

theorem cell22_1000641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1000641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000641 prefixEnd_1000641 := by exact prefixLift 1000641
  have htrace : WordTrace (prefixWord ++ tailWord_1000641) baseStart_1000641 baseEnd_1000641 := by
    simpa [prefixWord, tailWord_1000641, baseEnd_1000641] using wordTrace_append hprefix tailTrace_1000641
  have hstable : (prefixWord ++ tailWord_1000641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000641).length < 2 ^ (prefixWord ++ tailWord_1000641).sum := by decide
  have hdescent : baseEnd_1000641 < baseStart_1000641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000676 : List Nat := [2, 3, 1, 1, 1, 2, 2, 10]
def baseStart_1000676 : Nat := 118140960795 + 1000676 * 2 ^ 59
def prefixEnd_1000676 : Nat := 4983230072969 + 3 ^ 40 * 1000676 * 2
def baseEnd_1000676 : Nat := 38061316105083858092443

theorem tailTrace_1000676 : CollatzResearch.WordTrace tailWord_1000676 prefixEnd_1000676 38061316105083858092443 := by
  unfold tailWord_1000676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18248826061364614349858941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24331768081819485799811921 18248826061364614349858941)
  ·
    refine ⟨6843309773011730381197103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18248826061364614349858941 6843309773011730381197103)
    ·
      refine ⟨10264964659517595571795655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6843309773011730381197103 10264964659517595571795655)
      ·
        refine ⟨15397446989276393357693483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264964659517595571795655 15397446989276393357693483)
        ·
          refine ⟨23096170483914590036540225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15397446989276393357693483 23096170483914590036540225)
          ·
            refine ⟨17322127862935942527405169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23096170483914590036540225 17322127862935942527405169)
            ·
              refine ⟨12991595897201956895553877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17322127862935942527405169 12991595897201956895553877)
              ·
                refine ⟨38061316105083858092443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12991595897201956895553877 38061316105083858092443)
                ·
                  rfl

theorem cell22_1000676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 10].length) (baseStart_1000676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000676 prefixEnd_1000676 := by exact prefixLift 1000676
  have htrace : WordTrace (prefixWord ++ tailWord_1000676) baseStart_1000676 baseEnd_1000676 := by
    simpa [prefixWord, tailWord_1000676, baseEnd_1000676] using wordTrace_append hprefix tailTrace_1000676
  have hstable : (prefixWord ++ tailWord_1000676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000676).length < 2 ^ (prefixWord ++ tailWord_1000676).sum := by decide
  have hdescent : baseEnd_1000676 < baseStart_1000676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000768 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_1000768 : Nat := 118140960795 + 1000768 * 2 ^ 59
def prefixEnd_1000768 : Nat := 4983230072969 + 3 ^ 40 * 1000768 * 2
def baseEnd_1000768 : Nat := 342583338425897149531705

theorem tailTrace_1000768 : CollatzResearch.WordTrace tailWord_1000768 prefixEnd_1000768 342583338425897149531705 := by
  unfold tailWord_1000768
  simp only [CollatzResearch.WordTrace]
  refine ⟨18250503819197964206033479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24334005092263952274711305 18250503819197964206033479)
  ·
    refine ⟨27375755728796946309050219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18250503819197964206033479 27375755728796946309050219)
    ·
      refine ⟨41063633593195419463575329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27375755728796946309050219 41063633593195419463575329)
      ·
        refine ⟨30797725194896564597681497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41063633593195419463575329 30797725194896564597681497)
        ·
          refine ⟨23098293896172423448261123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30797725194896564597681497 23098293896172423448261123)
          ·
            refine ⟨34647440844258635172391685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23098293896172423448261123 34647440844258635172391685)
            ·
              refine ⟨6496395158298494094823441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34647440844258635172391685 6496395158298494094823441)
              ·
                refine ⟨4872296368723870571117581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6496395158298494094823441 4872296368723870571117581)
                ·
                  refine ⟨1827111138271451464169093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4872296368723870571117581 1827111138271451464169093)
                  ·
                    refine ⟨342583338425897149531705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1827111138271451464169093 342583338425897149531705)
                    ·
                      rfl

theorem cell22_1000768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_1000768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000768 prefixEnd_1000768 := by exact prefixLift 1000768
  have htrace : WordTrace (prefixWord ++ tailWord_1000768) baseStart_1000768 baseEnd_1000768 := by
    simpa [prefixWord, tailWord_1000768, baseEnd_1000768] using wordTrace_append hprefix tailTrace_1000768
  have hstable : (prefixWord ++ tailWord_1000768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000768).length < 2 ^ (prefixWord ++ tailWord_1000768).sum := by decide
  have hdescent : baseEnd_1000768 < baseStart_1000768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000772 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 5]
def baseStart_1000772 : Nat := 118140960795 + 1000772 * 2 ^ 59
def prefixEnd_1000772 : Nat := 4983230072969 + 3 ^ 40 * 1000772 * 2
def baseEnd_1000772 : Nat := 114194902569214157477231

theorem tailTrace_1000772 : CollatzResearch.WordTrace tailWord_1000772 prefixEnd_1000772 114194902569214157477231 := by
  unfold tailWord_1000772
  simp only [CollatzResearch.WordTrace]
  refine ⟨18250576765190718547606285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24334102353587624730141713 18250576765190718547606285)
  ·
    refine ⟨6843966286946519455352357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18250576765190718547606285 6843966286946519455352357)
    ·
      refine ⟨1283243678802472397878567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6843966286946519455352357 1283243678802472397878567)
      ·
        refine ⟨1924865518203708596817851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283243678802472397878567 1924865518203708596817851)
        ·
          refine ⟨2887298277305562895226777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924865518203708596817851 2887298277305562895226777)
          ·
            refine ⟨2165473707979172171420083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887298277305562895226777 2165473707979172171420083)
            ·
              refine ⟨3248210561968758257130125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165473707979172171420083 3248210561968758257130125)
              ·
                refine ⟨1218078960738284346423797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3248210561968758257130125 1218078960738284346423797)
                ·
                  refine ⟨114194902569214157477231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1218078960738284346423797 114194902569214157477231)
                  ·
                    rfl

theorem cell22_1000772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_1000772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000772 prefixEnd_1000772 := by exact prefixLift 1000772
  have htrace : WordTrace (prefixWord ++ tailWord_1000772) baseStart_1000772 baseEnd_1000772 := by
    simpa [prefixWord, tailWord_1000772, baseEnd_1000772] using wordTrace_append hprefix tailTrace_1000772
  have hstable : (prefixWord ++ tailWord_1000772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000772).length < 2 ^ (prefixWord ++ tailWord_1000772).sum := by decide
  have hdescent : baseEnd_1000772 < baseStart_1000772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000817 : List Nat := [1, 2, 2, 2, 1, 2, 6, 2, 4]
def baseStart_1000817 : Nat := 118140960795 + 1000817 * 2 ^ 59
def prefixEnd_1000817 : Nat := 4983230072969 + 3 ^ 40 * 1000817 * 2
def baseEnd_1000817 : Nat := 114200037375759118352185

theorem tailTrace_1000817 : CollatzResearch.WordTrace tailWord_1000817 prefixEnd_1000817 114200037375759118352185 := by
  unfold tailWord_1000817
  simp only [CollatzResearch.WordTrace]
  refine ⟨36502794815218409780600705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24335196543478939853733803 36502794815218409780600705)
  ·
    refine ⟨27377096111413807335450529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36502794815218409780600705 27377096111413807335450529)
    ·
      refine ⟨20532822083560355501587897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27377096111413807335450529 20532822083560355501587897)
      ·
        refine ⟨15399616562670266626190923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20532822083560355501587897 15399616562670266626190923)
        ·
          refine ⟨23099424844005399939286385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15399616562670266626190923 23099424844005399939286385)
          ·
            refine ⟨17324568633004049954464789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23099424844005399939286385 17324568633004049954464789)
            ·
              refine ⟨812089154672064841615537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17324568633004049954464789 812089154672064841615537)
              ·
                refine ⟨609066866004048631211653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812089154672064841615537 609066866004048631211653)
                ·
                  refine ⟨114200037375759118352185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609066866004048631211653 114200037375759118352185)
                  ·
                    rfl

theorem cell22_1000817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 4].length) (baseStart_1000817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000817 prefixEnd_1000817 := by exact prefixLift 1000817
  have htrace : WordTrace (prefixWord ++ tailWord_1000817) baseStart_1000817 baseEnd_1000817 := by
    simpa [prefixWord, tailWord_1000817, baseEnd_1000817] using wordTrace_append hprefix tailTrace_1000817
  have hstable : (prefixWord ++ tailWord_1000817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000817).length < 2 ^ (prefixWord ++ tailWord_1000817).sum := by decide
  have hdescent : baseEnd_1000817 < baseStart_1000817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000862 : List Nat := [4, 3, 1, 2, 2, 1, 9]
def baseStart_1000862 : Nat := 118140960795 + 1000862 * 2 ^ 59
def prefixEnd_1000862 : Nat := 4983230072969 + 3 ^ 40 * 1000862 * 2
def baseEnd_1000862 : Nat := 12689463575811564358571

theorem tailTrace_1000862 : CollatzResearch.WordTrace tailWord_1000862 prefixEnd_1000862 12689463575811564358571 := by
  unfold tailWord_1000862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563054512506922808248605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24336290733370254977325893 4563054512506922808248605)
  ·
    refine ⟨1711145442190096053093227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4563054512506922808248605 1711145442190096053093227)
    ·
      refine ⟨2566718163285144079639841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711145442190096053093227 2566718163285144079639841)
      ·
        refine ⟨1925038622463858059729881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2566718163285144079639841 1925038622463858059729881)
        ·
          refine ⟨1443778966847893544797411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1925038622463858059729881 1443778966847893544797411)
          ·
            refine ⟨2165668450271840317196117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443778966847893544797411 2165668450271840317196117)
            ·
              refine ⟨12689463575811564358571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2165668450271840317196117 12689463575811564358571)
              ·
                rfl

theorem cell22_1000862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 9].length) (baseStart_1000862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000862 prefixEnd_1000862 := by exact prefixLift 1000862
  have htrace : WordTrace (prefixWord ++ tailWord_1000862) baseStart_1000862 baseEnd_1000862 := by
    simpa [prefixWord, tailWord_1000862, baseEnd_1000862] using wordTrace_append hprefix tailTrace_1000862
  have hstable : (prefixWord ++ tailWord_1000862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000862).length < 2 ^ (prefixWord ++ tailWord_1000862).sum := by decide
  have hdescent : baseEnd_1000862 < baseStart_1000862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000941 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1000941 : Nat := 118140960795 + 1000941 * 2 ^ 59
def prefixEnd_1000941 : Nat := 4983230072969 + 3 ^ 40 * 1000941 * 2
def baseEnd_1000941 : Nat := 114214186620460788318725

theorem tailTrace_1000941 : CollatzResearch.WordTrace tailWord_1000941 prefixEnd_1000941 114214186620460788318725 := by
  unfold tailWord_1000941
  simp only [CollatzResearch.WordTrace]
  refine ⟨36507317466769178958114677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24338211644512785972076451 36507317466769178958114677)
  ·
    refine ⟨3422561012509610527323251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36507317466769178958114677 3422561012509610527323251)
    ·
      refine ⟨5133841518764415790984877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422561012509610527323251 5133841518764415790984877)
      ·
        refine ⟨1925190569536655921619329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5133841518764415790984877 1925190569536655921619329)
        ·
          refine ⟨1443892927152491941214497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1925190569536655921619329 1443892927152491941214497)
          ·
            refine ⟨1082919695364368955910873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443892927152491941214497 1082919695364368955910873)
            ·
              refine ⟨812189771523276716933155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082919695364368955910873 812189771523276716933155)
              ·
                refine ⟨1218284657284915075399733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812189771523276716933155 1218284657284915075399733)
                ·
                  refine ⟨114214186620460788318725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1218284657284915075399733 114214186620460788318725)
                  ·
                    rfl

theorem cell22_1000941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1000941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000941 prefixEnd_1000941 := by exact prefixLift 1000941
  have htrace : WordTrace (prefixWord ++ tailWord_1000941) baseStart_1000941 baseEnd_1000941 := by
    simpa [prefixWord, tailWord_1000941, baseEnd_1000941] using wordTrace_append hprefix tailTrace_1000941
  have hstable : (prefixWord ++ tailWord_1000941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000941).length < 2 ^ (prefixWord ++ tailWord_1000941).sum := by decide
  have hdescent : baseEnd_1000941 < baseStart_1000941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000967 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1000967 : Nat := 118140960795 + 1000967 * 2 ^ 59
def prefixEnd_1000967 : Nat := 4983230072969 + 3 ^ 40 * 1000967 * 2
def baseEnd_1000967 : Nat := 342651460192726963806095

theorem tailTrace_1000967 : CollatzResearch.WordTrace tailWord_1000967 prefixEnd_1000967 342651460192726963806095 := by
  unfold tailWord_1000967
  simp only [CollatzResearch.WordTrace]
  refine ⟨36508265764674985398561155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24338843843116656932374103 36508265764674985398561155)
  ·
    refine ⟨54762398647012478097841733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36508265764674985398561155 54762398647012478097841733)
    ·
      refine ⟨10267949746314839643345325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54762398647012478097841733 10267949746314839643345325)
      ·
        refine ⟨3850481154868064866254497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10267949746314839643345325 3850481154868064866254497)
        ·
          refine ⟨2887860866151048649690873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3850481154868064866254497 2887860866151048649690873)
          ·
            refine ⟨2165895649613286487268155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887860866151048649690873 2165895649613286487268155)
            ·
              refine ⟨3248843474419929730902233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165895649613286487268155 3248843474419929730902233)
              ·
                refine ⟨2436632605814947298176675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3248843474419929730902233 2436632605814947298176675)
                ·
                  refine ⟨3654948908722420947265013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436632605814947298176675 3654948908722420947265013)
                  ·
                    refine ⟨342651460192726963806095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3654948908722420947265013 342651460192726963806095)
                    ·
                      rfl

theorem cell22_1000967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1000967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1000967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1000967 prefixEnd_1000967 := by exact prefixLift 1000967
  have htrace : WordTrace (prefixWord ++ tailWord_1000967) baseStart_1000967 baseEnd_1000967 := by
    simpa [prefixWord, tailWord_1000967, baseEnd_1000967] using wordTrace_append hprefix tailTrace_1000967
  have hstable : (prefixWord ++ tailWord_1000967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000967).length < 2 ^ (prefixWord ++ tailWord_1000967).sum := by decide
  have hdescent : baseEnd_1000967 < baseStart_1000967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001010 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1001010 : Nat := 118140960795 + 1001010 * 2 ^ 59
def prefixEnd_1001010 : Nat := 4983230072969 + 3 ^ 40 * 1001010 * 2
def baseEnd_1001010 : Nat := 342666179971489184980963

theorem tailTrace_1001010 : CollatzResearch.WordTrace tailWord_1001010 prefixEnd_1001010 342666179971489184980963 := by
  unfold tailWord_1001010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127458525879800935594121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24339889402346135828250989 9127458525879800935594121)
  ·
    refine ⟨6845593894409850701695591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9127458525879800935594121 6845593894409850701695591)
    ·
      refine ⟨10268390841614776052543387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6845593894409850701695591 10268390841614776052543387)
      ·
        refine ⟨15402586262422164078815081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10268390841614776052543387 15402586262422164078815081)
        ·
          refine ⟨11551939696816623059111311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15402586262422164078815081 11551939696816623059111311)
          ·
            refine ⟨17327909545224934588666967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551939696816623059111311 17327909545224934588666967)
            ·
              refine ⟨25991864317837401883000451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17327909545224934588666967 25991864317837401883000451)
              ·
                refine ⟨38987796476756102824500677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25991864317837401883000451 38987796476756102824500677)
                ·
                  refine ⟨7310211839391769279593877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38987796476756102824500677 7310211839391769279593877)
                  ·
                    refine ⟨342666179971489184980963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7310211839391769279593877 342666179971489184980963)
                    ·
                      rfl

theorem cell22_1001010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1001010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001010 prefixEnd_1001010 := by exact prefixLift 1001010
  have htrace : WordTrace (prefixWord ++ tailWord_1001010) baseStart_1001010 baseEnd_1001010 := by
    simpa [prefixWord, tailWord_1001010, baseEnd_1001010] using wordTrace_append hprefix tailTrace_1001010
  have hstable : (prefixWord ++ tailWord_1001010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001010).length < 2 ^ (prefixWord ++ tailWord_1001010).sum := by decide
  have hdescent : baseEnd_1001010 < baseStart_1001010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001040 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_1001040 : Nat := 118140960795 + 1001040 * 2 ^ 59
def prefixEnd_1001040 : Nat := 4983230072969 + 3 ^ 40 * 1001040 * 2
def baseEnd_1001040 : Nat := 342676449584579106730871

theorem tailTrace_1001040 : CollatzResearch.WordTrace tailWord_1001040 prefixEnd_1001040 342676449584579106730871 := by
  unfold tailWord_1001040
  simp only [CollatzResearch.WordTrace]
  refine ⟨18255464146705259432984287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24340618862273679243979049 18255464146705259432984287)
  ·
    refine ⟨27383196220057889149476431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18255464146705259432984287 27383196220057889149476431)
    ·
      refine ⟨41074794330086833724214647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27383196220057889149476431 41074794330086833724214647)
      ·
        refine ⟨61612191495130250586321971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41074794330086833724214647 61612191495130250586321971)
        ·
          refine ⟨92418287242695375879482957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61612191495130250586321971 92418287242695375879482957)
          ·
            refine ⟨34656857716010765954806109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92418287242695375879482957 34656857716010765954806109)
            ·
              refine ⟨12996321643504037233052291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34656857716010765954806109 12996321643504037233052291)
              ·
                refine ⟨19494482465256055849578437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12996321643504037233052291 19494482465256055849578437)
                ·
                  refine ⟨3655215462235510471795957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19494482465256055849578437 3655215462235510471795957)
                  ·
                    refine ⟨342676449584579106730871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3655215462235510471795957 342676449584579106730871)
                    ·
                      rfl

theorem cell22_1001040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_1001040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001040 prefixEnd_1001040 := by exact prefixLift 1001040
  have htrace : WordTrace (prefixWord ++ tailWord_1001040) baseStart_1001040 baseEnd_1001040 := by
    simpa [prefixWord, tailWord_1001040, baseEnd_1001040] using wordTrace_append hprefix tailTrace_1001040
  have hstable : (prefixWord ++ tailWord_1001040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001040).length < 2 ^ (prefixWord ++ tailWord_1001040).sum := by decide
  have hdescent : baseEnd_1001040 < baseStart_1001040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001042 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_1001042 : Nat := 118140960795 + 1001042 * 2 ^ 59
def prefixEnd_1001042 : Nat := 4983230072969 + 3 ^ 40 * 1001042 * 2
def baseEnd_1001042 : Nat := 114225711408483922726955

theorem tailTrace_1001042 : CollatzResearch.WordTrace tailWord_1001042 prefixEnd_1001042 114225711408483922726955 := by
  unfold tailWord_1001042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127750309850818301885345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24340667492935515471694253 9127750309850818301885345)
  ·
    refine ⟨6845812732388113726414009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9127750309850818301885345 6845812732388113726414009)
    ·
      refine ⟨5134359549291085294810507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6845812732388113726414009 5134359549291085294810507)
      ·
        refine ⟨7701539323936627942215761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134359549291085294810507 7701539323936627942215761)
        ·
          refine ⟨5776154492952470956661821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7701539323936627942215761 5776154492952470956661821)
          ·
            refine ⟨2166057934857176608748183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5776154492952470956661821 2166057934857176608748183)
            ·
              refine ⟨3249086902285764913122275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166057934857176608748183 3249086902285764913122275)
              ·
                refine ⟨4873630353428647369683413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249086902285764913122275 4873630353428647369683413)
                ·
                  refine ⟨114225711408483922726955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4873630353428647369683413 114225711408483922726955)
                  ·
                    rfl

theorem cell22_1001042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_1001042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001042 prefixEnd_1001042 := by exact prefixLift 1001042
  have htrace : WordTrace (prefixWord ++ tailWord_1001042) baseStart_1001042 baseEnd_1001042 := by
    simpa [prefixWord, tailWord_1001042, baseEnd_1001042] using wordTrace_append hprefix tailTrace_1001042
  have hstable : (prefixWord ++ tailWord_1001042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001042).length < 2 ^ (prefixWord ++ tailWord_1001042).sum := by decide
  have hdescent : baseEnd_1001042 < baseStart_1001042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001059 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 5]
def baseStart_1001059 : Nat := 118140960795 + 1001059 * 2 ^ 59
def prefixEnd_1001059 : Nat := 4983230072969 + 3 ^ 40 * 1001059 * 2
def baseEnd_1001059 : Nat := 114227651224289796835271

theorem tailTrace_1001059 : CollatzResearch.WordTrace tailWord_1001059 prefixEnd_1001059 114227651224289796835271 := by
  unfold tailWord_1001059
  simp only [CollatzResearch.WordTrace]
  refine ⟨36511621280341685110910231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24341080853561123407273487 36511621280341685110910231)
  ·
    refine ⟨54767431920512527666365347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36511621280341685110910231 54767431920512527666365347)
    ·
      refine ⟨82151147880768791499548021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54767431920512527666365347 82151147880768791499548021)
      ·
        refine ⟨7701670113822074203082627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82151147880768791499548021 7701670113822074203082627)
        ·
          refine ⟨11552505170733111304623941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701670113822074203082627 11552505170733111304623941)
          ·
            refine ⟨2166094719512458369616989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11552505170733111304623941 2166094719512458369616989)
            ·
              refine ⟨812285519817171888606371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2166094719512458369616989 812285519817171888606371)
              ·
                refine ⟨1218428279725757832909557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812285519817171888606371 1218428279725757832909557)
                ·
                  refine ⟨114227651224289796835271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1218428279725757832909557 114227651224289796835271)
                  ·
                    rfl

theorem cell22_1001059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 5].length) (baseStart_1001059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001059 prefixEnd_1001059 := by exact prefixLift 1001059
  have htrace : WordTrace (prefixWord ++ tailWord_1001059) baseStart_1001059 baseEnd_1001059 := by
    simpa [prefixWord, tailWord_1001059, baseEnd_1001059] using wordTrace_append hprefix tailTrace_1001059
  have hstable : (prefixWord ++ tailWord_1001059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001059).length < 2 ^ (prefixWord ++ tailWord_1001059).sum := by decide
  have hdescent : baseEnd_1001059 < baseStart_1001059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001089 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1001089 : Nat := 118140960795 + 1001089 * 2 ^ 59
def prefixEnd_1001089 : Nat := 4983230072969 + 3 ^ 40 * 1001089 * 2
def baseEnd_1001089 : Nat := 342693223285959312255721

theorem tailTrace_1001089 : CollatzResearch.WordTrace tailWord_1001089 prefixEnd_1001089 342693223285959312255721 := by
  unfold tailWord_1001089
  simp only [CollatzResearch.WordTrace]
  refine ⟨36512715470233000234502321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24341810313488666823001547 36512715470233000234502321)
  ·
    refine ⟨27384536602674750175876741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36512715470233000234502321 27384536602674750175876741)
    ·
      refine ⟨5134600613001515657976889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27384536602674750175876741 5134600613001515657976889)
      ·
        refine ⟨3850950459751136743482667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5134600613001515657976889 3850950459751136743482667)
        ·
          refine ⟨5776425689626705115224001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850950459751136743482667 5776425689626705115224001)
          ·
            refine ⟨4332319267220028836418001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5776425689626705115224001 4332319267220028836418001)
            ·
              refine ⟨3249239450415021627313501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4332319267220028836418001 3249239450415021627313501)
              ·
                refine ⟨1218464793905633110242563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3249239450415021627313501 1218464793905633110242563)
                ·
                  refine ⟨1827697190858449665363845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218464793905633110242563 1827697190858449665363845)
                  ·
                    refine ⟨342693223285959312255721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1827697190858449665363845 342693223285959312255721)
                    ·
                      rfl

theorem cell22_1001089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1001089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001089 prefixEnd_1001089 := by exact prefixLift 1001089
  have htrace : WordTrace (prefixWord ++ tailWord_1001089) baseStart_1001089 baseEnd_1001089 := by
    simpa [prefixWord, tailWord_1001089, baseEnd_1001089] using wordTrace_append hprefix tailTrace_1001089
  have hstable : (prefixWord ++ tailWord_1001089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001089).length < 2 ^ (prefixWord ++ tailWord_1001089).sum := by decide
  have hdescent : baseEnd_1001089 < baseStart_1001089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001117 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1001117 : Nat := 118140960795 + 1001117 * 2 ^ 59
def prefixEnd_1001117 : Nat := 4983230072969 + 3 ^ 40 * 1001117 * 2
def baseEnd_1001117 : Nat := 342702808258176572555635

theorem tailTrace_1001117 : CollatzResearch.WordTrace tailWord_1001117 prefixEnd_1001117 342702808258176572555635 := by
  unfold tailWord_1001117
  simp only [CollatzResearch.WordTrace]
  refine ⟨36513736714131561016521605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24342491142754374011014403 36513736714131561016521605)
  ·
    refine ⟨6846325633899667690597801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36513736714131561016521605 6846325633899667690597801)
    ·
      refine ⟨5134744225424750767948351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6846325633899667690597801 5134744225424750767948351)
      ·
        refine ⟨7702116338137126151922527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134744225424750767948351 7702116338137126151922527)
        ·
          refine ⟨11553174507205689227883791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7702116338137126151922527 11553174507205689227883791)
          ·
            refine ⟨17329761760808533841825687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11553174507205689227883791 17329761760808533841825687)
            ·
              refine ⟨25994642641212800762738531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17329761760808533841825687 25994642641212800762738531)
              ·
                refine ⟨38991963961819201144107797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25994642641212800762738531 38991963961819201144107797)
                ·
                  refine ⟨1827748310710275053630053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38991963961819201144107797 1827748310710275053630053)
                  ·
                    refine ⟨342702808258176572555635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1827748310710275053630053 342702808258176572555635)
                    ·
                      rfl

theorem cell22_1001117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1001117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001117 prefixEnd_1001117 := by exact prefixLift 1001117
  have htrace : WordTrace (prefixWord ++ tailWord_1001117) baseStart_1001117 baseEnd_1001117 := by
    simpa [prefixWord, tailWord_1001117, baseEnd_1001117] using wordTrace_append hprefix tailTrace_1001117
  have hstable : (prefixWord ++ tailWord_1001117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001117).length < 2 ^ (prefixWord ++ tailWord_1001117).sum := by decide
  have hdescent : baseEnd_1001117 < baseStart_1001117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001198 : List Nat := [4, 1, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1001198 : Nat := 118140960795 + 1001198 * 2 ^ 59
def prefixEnd_1001198 : Nat := 4983230072969 + 3 ^ 40 * 1001198 * 2
def baseEnd_1001198 : Nat := 342730536213519361280387

theorem tailTrace_1001198 : CollatzResearch.WordTrace tailWord_1001198 prefixEnd_1001198 342730536213519361280387 := by
  unfold tailWord_1001198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564586378354763981277531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24344460684558741233480165 4564586378354763981277531)
  ·
    refine ⟨6846879567532145971916297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4564586378354763981277531 6846879567532145971916297)
    ·
      refine ⟨5135159675649109478937223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6846879567532145971916297 5135159675649109478937223)
      ·
        refine ⟨7702739513473664218405835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5135159675649109478937223 7702739513473664218405835)
        ·
          refine ⟨11554109270210496327608753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7702739513473664218405835 11554109270210496327608753)
          ·
            refine ⟨8665581952657872245706565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11554109270210496327608753 8665581952657872245706565)
            ·
              refine ⟨1624796616123351046069981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8665581952657872245706565 1624796616123351046069981)
              ·
                refine ⟨609298731046256642276243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1624796616123351046069981 609298731046256642276243)
                ·
                  refine ⟨913948096569384963414365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609298731046256642276243 913948096569384963414365)
                  ·
                    refine ⟨342730536213519361280387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913948096569384963414365 342730536213519361280387)
                    ·
                      rfl

theorem cell22_1001198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1001198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001198 prefixEnd_1001198 := by exact prefixLift 1001198
  have htrace : WordTrace (prefixWord ++ tailWord_1001198) baseStart_1001198 baseEnd_1001198 := by
    simpa [prefixWord, tailWord_1001198, baseEnd_1001198] using wordTrace_append hprefix tailTrace_1001198
  have hstable : (prefixWord ++ tailWord_1001198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001198).length < 2 ^ (prefixWord ++ tailWord_1001198).sum := by decide
  have hdescent : baseEnd_1001198 < baseStart_1001198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001239 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 6]
def baseStart_1001239 : Nat := 118140960795 + 1001239 * 2 ^ 59
def prefixEnd_1001239 : Nat := 4983230072969 + 3 ^ 40 * 1001239 * 2
def baseEnd_1001239 : Nat := 114248190450469640335087

theorem tailTrace_1001239 : CollatzResearch.WordTrace tailWord_1001239 prefixEnd_1001239 114248190450469640335087 := by
  unfold tailWord_1001239
  simp only [CollatzResearch.WordTrace]
  refine ⟨36518186419689575852462771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24345457613126383901641847 36518186419689575852462771)
  ·
    refine ⟨54777279629534363778694157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36518186419689575852462771 54777279629534363778694157)
    ·
      refine ⟨20541479861075386417010309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54777279629534363778694157 20541479861075386417010309)
      ·
        refine ⟨3851527473951634953189433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20541479861075386417010309 3851527473951634953189433)
        ·
          refine ⟨2888645605463726214892075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3851527473951634953189433 2888645605463726214892075)
          ·
            refine ⟨4332968408195589322338113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888645605463726214892075 4332968408195589322338113)
            ·
              refine ⟨3249726306146691991753585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4332968408195589322338113 3249726306146691991753585)
              ·
                refine ⟨2437294729610018993815189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3249726306146691991753585 2437294729610018993815189)
                ·
                  refine ⟨114248190450469640335087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2437294729610018993815189 114248190450469640335087)
                  ·
                    rfl

theorem cell22_1001239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 6].length) (baseStart_1001239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001239 prefixEnd_1001239 := by exact prefixLift 1001239
  have htrace : WordTrace (prefixWord ++ tailWord_1001239) baseStart_1001239 baseEnd_1001239 := by
    simpa [prefixWord, tailWord_1001239, baseEnd_1001239] using wordTrace_append hprefix tailTrace_1001239
  have hstable : (prefixWord ++ tailWord_1001239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001239).length < 2 ^ (prefixWord ++ tailWord_1001239).sum := by decide
  have hdescent : baseEnd_1001239 < baseStart_1001239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001273 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 6]
def baseStart_1001273 : Nat := 118140960795 + 1001273 * 2 ^ 59
def prefixEnd_1001273 : Nat := 4983230072969 + 3 ^ 40 * 1001273 * 2
def baseEnd_1001273 : Nat := 114252070082081388551719

theorem tailTrace_1001273 : CollatzResearch.WordTrace tailWord_1001273 prefixEnd_1001273 114252070082081388551719 := by
  unfold tailWord_1001273
  simp only [CollatzResearch.WordTrace]
  refine ⟨36519426501566399659200473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24346284334377599772800315 36519426501566399659200473)
  ·
    refine ⟨27389569876174799744400355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36519426501566399659200473 27389569876174799744400355)
    ·
      refine ⟨41084354814262199616600533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27389569876174799744400355 41084354814262199616600533)
      ·
        refine ⟨962914565959270303514075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41084354814262199616600533 962914565959270303514075)
        ·
          refine ⟨1444371848938905455271113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962914565959270303514075 1444371848938905455271113)
          ·
            refine ⟨1083278886704179091453335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444371848938905455271113 1083278886704179091453335)
            ·
              refine ⟨1624918330056268637180003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083278886704179091453335 1624918330056268637180003)
              ·
                refine ⟨2437377495084402955770005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624918330056268637180003 2437377495084402955770005)
                ·
                  refine ⟨114252070082081388551719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2437377495084402955770005 114252070082081388551719)
                  ·
                    rfl

theorem cell22_1001273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_1001273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001273 prefixEnd_1001273 := by exact prefixLift 1001273
  have htrace : WordTrace (prefixWord ++ tailWord_1001273) baseStart_1001273 baseEnd_1001273 := by
    simpa [prefixWord, tailWord_1001273, baseEnd_1001273] using wordTrace_append hprefix tailTrace_1001273
  have hstable : (prefixWord ++ tailWord_1001273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001273).length < 2 ^ (prefixWord ++ tailWord_1001273).sum := by decide
  have hdescent : baseEnd_1001273 < baseStart_1001273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001288 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 2, 3]
def baseStart_1001288 : Nat := 118140960795 + 1001288 * 2 ^ 59
def prefixEnd_1001288 : Nat := 4983230072969 + 3 ^ 40 * 1001288 * 2
def baseEnd_1001288 : Nat := 342761345052789126530111

theorem tailTrace_1001288 : CollatzResearch.WordTrace tailWord_1001288 prefixEnd_1001288 342761345052789126530111 := by
  unfold tailWord_1001288
  simp only [CollatzResearch.WordTrace]
  refine ⟨18259986798256028610498259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24346649064341371480664345 18259986798256028610498259)
  ·
    refine ⟨27389980197384042915747389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18259986798256028610498259 27389980197384042915747389)
    ·
      refine ⟨10271242574019016093405271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27389980197384042915747389 10271242574019016093405271)
      ·
        refine ⟨15406863861028524140107907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10271242574019016093405271 15406863861028524140107907)
        ·
          refine ⟨23110295791542786210161861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15406863861028524140107907 23110295791542786210161861)
          ·
            refine ⟨4333180460914272414405349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23110295791542786210161861 4333180460914272414405349)
            ·
              refine ⟨812471336421426077701003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4333180460914272414405349 812471336421426077701003)
              ·
                refine ⟨1218707004632139116551505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812471336421426077701003 1218707004632139116551505)
                ·
                  refine ⟨914030253474104337413629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218707004632139116551505 914030253474104337413629)
                  ·
                    refine ⟨342761345052789126530111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914030253474104337413629 342761345052789126530111)
                    ·
                      rfl

theorem cell22_1001288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_1001288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001288 prefixEnd_1001288 := by exact prefixLift 1001288
  have htrace : WordTrace (prefixWord ++ tailWord_1001288) baseStart_1001288 baseEnd_1001288 := by
    simpa [prefixWord, tailWord_1001288, baseEnd_1001288] using wordTrace_append hprefix tailTrace_1001288
  have hstable : (prefixWord ++ tailWord_1001288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001288).length < 2 ^ (prefixWord ++ tailWord_1001288).sum := by decide
  have hdescent : baseEnd_1001288 < baseStart_1001288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001344 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_1001344 : Nat := 118140960795 + 1001344 * 2 ^ 59
def prefixEnd_1001344 : Nat := 4983230072969 + 3 ^ 40 * 1001344 * 2
def baseEnd_1001344 : Nat := 342780514997223647129939

theorem tailTrace_1001344 : CollatzResearch.WordTrace tailWord_1001344 prefixEnd_1001344 342780514997223647129939 := by
  unfold tailWord_1001344
  simp only [CollatzResearch.WordTrace]
  refine ⟨18261008042154589392517543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24348010722872785856690057 18261008042154589392517543)
  ·
    refine ⟨27391512063231884088776315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18261008042154589392517543 27391512063231884088776315)
    ·
      refine ⟨41087268094847826133164473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27391512063231884088776315 41087268094847826133164473)
      ·
        refine ⟨30815451071135869599873355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41087268094847826133164473 30815451071135869599873355)
        ·
          refine ⟨46223176606703804399810033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30815451071135869599873355 46223176606703804399810033)
          ·
            refine ⟨34667382455027853299857525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46223176606703804399810033 34667382455027853299857525)
            ·
              refine ⟨3250067105158861246861643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34667382455027853299857525 3250067105158861246861643)
              ·
                refine ⟨4875100657738291870292465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250067105158861246861643 4875100657738291870292465)
                ·
                  refine ⟨3656325493303718902719349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4875100657738291870292465 3656325493303718902719349)
                  ·
                    refine ⟨342780514997223647129939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3656325493303718902719349 342780514997223647129939)
                    ·
                      rfl

theorem cell22_1001344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_1001344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001344 prefixEnd_1001344 := by exact prefixLift 1001344
  have htrace : WordTrace (prefixWord ++ tailWord_1001344) baseStart_1001344 baseEnd_1001344 := by
    simpa [prefixWord, tailWord_1001344, baseEnd_1001344] using wordTrace_append hprefix tailTrace_1001344
  have hstable : (prefixWord ++ tailWord_1001344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001344).length < 2 ^ (prefixWord ++ tailWord_1001344).sum := by decide
  have hdescent : baseEnd_1001344 < baseStart_1001344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001391 : List Nat := [1, 1, 2, 1, 2, 2, 3, 6, 4]
def baseStart_1001391 : Nat := 118140960795 + 1001391 * 2 ^ 59
def prefixEnd_1001391 : Nat := 4983230072969 + 3 ^ 40 * 1001391 * 2
def baseEnd_1001391 : Nat := 114265534685910397068265

theorem tailTrace_1001391 : CollatzResearch.WordTrace tailWord_1001391 prefixEnd_1001391 114265534685910397068265 := by
  unfold tailWord_1001391
  simp only [CollatzResearch.WordTrace]
  refine ⟨36523730315138905811996027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24349153543425937207997351 36523730315138905811996027)
  ·
    refine ⟨54785595472708358717994041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36523730315138905811996027 54785595472708358717994041)
    ·
      refine ⟨41089196604531269038495531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54785595472708358717994041 41089196604531269038495531)
      ·
        refine ⟨61633794906796903557743297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41089196604531269038495531 61633794906796903557743297)
        ·
          refine ⟨46225346180097677668307473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61633794906796903557743297 46225346180097677668307473)
          ·
            refine ⟨34669009635073258251230605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46225346180097677668307473 34669009635073258251230605)
            ·
              refine ⟨13000878613152471844211477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34669009635073258251230605 13000878613152471844211477)
              ·
                refine ⟨609416184991522117697413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13000878613152471844211477 609416184991522117697413)
                ·
                  refine ⟨114265534685910397068265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609416184991522117697413 114265534685910397068265)
                  ·
                    rfl

theorem cell22_1001391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 4].length) (baseStart_1001391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001391 prefixEnd_1001391 := by exact prefixLift 1001391
  have htrace : WordTrace (prefixWord ++ tailWord_1001391) baseStart_1001391 baseEnd_1001391 := by
    simpa [prefixWord, tailWord_1001391, baseEnd_1001391] using wordTrace_append hprefix tailTrace_1001391
  have hstable : (prefixWord ++ tailWord_1001391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001391).length < 2 ^ (prefixWord ++ tailWord_1001391).sum := by decide
  have hdescent : baseEnd_1001391 < baseStart_1001391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001419 : List Nat := [1, 1, 1, 1, 3, 4, 3, 8]
def baseStart_1001419 : Nat := 118140960795 + 1001419 * 2 ^ 59
def prefixEnd_1001419 : Nat := 4983230072969 + 3 ^ 40 * 1001419 * 2
def baseEnd_1001419 : Nat := 38089576558883161278301

theorem tailTrace_1001419 : CollatzResearch.WordTrace tailWord_1001419 prefixEnd_1001419 38089576558883161278301 := by
  unfold tailWord_1001419
  simp only [CollatzResearch.WordTrace]
  refine ⟨36524751559037466594015311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24349834372691644396010207 36524751559037466594015311)
  ·
    refine ⟨54787127338556199891022967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36524751559037466594015311 54787127338556199891022967)
    ·
      refine ⟨82180691007834299836534451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54787127338556199891022967 82180691007834299836534451)
      ·
        refine ⟨123271036511751449754801677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82180691007834299836534451 123271036511751449754801677)
        ·
          refine ⟨46226638691906793658050629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123271036511751449754801677 46226638691906793658050629)
          ·
            refine ⟨8667494754732523810884493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46226638691906793658050629 8667494754732523810884493)
            ·
              refine ⟨3250310533024696429081685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8667494754732523810884493 3250310533024696429081685)
              ·
                refine ⟨38089576558883161278301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3250310533024696429081685 38089576558883161278301)
                ·
                  rfl

theorem cell22_1001419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 8].length) (baseStart_1001419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001419 prefixEnd_1001419 := by exact prefixLift 1001419
  have htrace : WordTrace (prefixWord ++ tailWord_1001419) baseStart_1001419 baseEnd_1001419 := by
    simpa [prefixWord, tailWord_1001419, baseEnd_1001419] using wordTrace_append hprefix tailTrace_1001419
  have hstable : (prefixWord ++ tailWord_1001419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001419).length < 2 ^ (prefixWord ++ tailWord_1001419).sum := by decide
  have hdescent : baseEnd_1001419 < baseStart_1001419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001442 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_1001442 : Nat := 118140960795 + 1001442 * 2 ^ 59
def prefixEnd_1001442 : Nat := 4983230072969 + 3 ^ 40 * 1001442 * 2
def baseEnd_1001442 : Nat := 114271354133328019393213

theorem tailTrace_1001442 : CollatzResearch.WordTrace tailWord_1001442 prefixEnd_1001442 114271354133328019393213 := by
  unfold tailWord_1001442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9131397609488535380525645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24350393625302761014735053 9131397609488535380525645)
  ·
    refine ⟨3424274103558200767697117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9131397609488535380525645 3424274103558200767697117)
    ·
      refine ⟨1284102788834325287886419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3424274103558200767697117 1284102788834325287886419)
      ·
        refine ⟨1926154183251487931829629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284102788834325287886419 1926154183251487931829629)
        ·
          refine ⟨722307818719307974436111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1926154183251487931829629 722307818719307974436111)
          ·
            refine ⟨1083461728078961961654167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722307818719307974436111 1083461728078961961654167)
            ·
              refine ⟨1625192592118442942481251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083461728078961961654167 1625192592118442942481251)
              ·
                refine ⟨2437788888177664413721877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625192592118442942481251 2437788888177664413721877)
                ·
                  refine ⟨114271354133328019393213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2437788888177664413721877 114271354133328019393213)
                  ·
                    rfl

theorem cell22_1001442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_1001442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001442 prefixEnd_1001442 := by exact prefixLift 1001442
  have htrace : WordTrace (prefixWord ++ tailWord_1001442) baseStart_1001442 baseEnd_1001442 := by
    simpa [prefixWord, tailWord_1001442, baseEnd_1001442] using wordTrace_append hprefix tailTrace_1001442
  have hstable : (prefixWord ++ tailWord_1001442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001442).length < 2 ^ (prefixWord ++ tailWord_1001442).sum := by decide
  have hdescent : baseEnd_1001442 < baseStart_1001442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001457 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 2, 3]
def baseStart_1001457 : Nat := 118140960795 + 1001457 * 2 ^ 59
def prefixEnd_1001457 : Nat := 4983230072969 + 3 ^ 40 * 1001457 * 2
def baseEnd_1001457 : Nat := 342819197206529019054593

theorem tailTrace_1001457 : CollatzResearch.WordTrace tailWord_1001457 prefixEnd_1001457 342819197206529019054593 := by
  unfold tailWord_1001457
  simp only [CollatzResearch.WordTrace]
  refine ⟨36526137532899799083898625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24350758355266532722599083 36526137532899799083898625)
  ·
    refine ⟨27394603149674849312923969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36526137532899799083898625 27394603149674849312923969)
    ·
      refine ⟨20545952362256136984692977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27394603149674849312923969 20545952362256136984692977)
      ·
        refine ⟨15409464271692102738519733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20545952362256136984692977 15409464271692102738519733)
        ·
          refine ⟨1444637275471134631736225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15409464271692102738519733 1444637275471134631736225)
          ·
            refine ⟨1083477956603350973802169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444637275471134631736225 1083477956603350973802169)
            ·
              refine ⟨812608467452513230351627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083477956603350973802169 812608467452513230351627)
              ·
                refine ⟨1218912701178769845527441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812608467452513230351627 1218912701178769845527441)
                ·
                  refine ⟨914184525884077384145581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218912701178769845527441 914184525884077384145581)
                  ·
                    refine ⟨342819197206529019054593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914184525884077384145581 342819197206529019054593)
                    ·
                      rfl

theorem cell22_1001457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_1001457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001457 prefixEnd_1001457 := by exact prefixLift 1001457
  have htrace : WordTrace (prefixWord ++ tailWord_1001457) baseStart_1001457 baseEnd_1001457 := by
    simpa [prefixWord, tailWord_1001457, baseEnd_1001457] using wordTrace_append hprefix tailTrace_1001457
  have hstable : (prefixWord ++ tailWord_1001457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001457).length < 2 ^ (prefixWord ++ tailWord_1001457).sum := by decide
  have hdescent : baseEnd_1001457 < baseStart_1001457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001496 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1001496 : Nat := 118140960795 + 1001496 * 2 ^ 59
def prefixEnd_1001496 : Nat := 4983230072969 + 3 ^ 40 * 1001496 * 2
def baseEnd_1001496 : Nat := 342832547703545917329473

theorem tailTrace_1001496 : CollatzResearch.WordTrace tailWord_1001496 prefixEnd_1001496 342832547703545917329473 := by
  unfold tailWord_1001496
  simp only [CollatzResearch.WordTrace]
  refine ⟨18263779989879254372284171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24351706653172339163045561 18263779989879254372284171)
  ·
    refine ⟨27395669984818881558426257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18263779989879254372284171 27395669984818881558426257)
    ·
      refine ⟨20546752488614161168819693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27395669984818881558426257 20546752488614161168819693)
      ·
        refine ⟨7705032183230310438307385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20546752488614161168819693 7705032183230310438307385)
        ·
          refine ⟨5778774137422732828730539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7705032183230310438307385 5778774137422732828730539)
          ·
            refine ⟨8668161206134099243095809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778774137422732828730539 8668161206134099243095809)
            ·
              refine ⟨6501120904600574432321857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8668161206134099243095809 6501120904600574432321857)
              ·
                refine ⟨4875840678450430824241393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6501120904600574432321857 4875840678450430824241393)
                ·
                  refine ⟨3656880508837823118181045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4875840678450430824241393 3656880508837823118181045)
                  ·
                    refine ⟨342832547703545917329473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3656880508837823118181045 342832547703545917329473)
                    ·
                      rfl

theorem cell22_1001496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1001496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001496 prefixEnd_1001496 := by exact prefixLift 1001496
  have htrace : WordTrace (prefixWord ++ tailWord_1001496) baseStart_1001496 baseEnd_1001496 := by
    simpa [prefixWord, tailWord_1001496, baseEnd_1001496] using wordTrace_append hprefix tailTrace_1001496
  have hstable : (prefixWord ++ tailWord_1001496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001496).length < 2 ^ (prefixWord ++ tailWord_1001496).sum := by decide
  have hdescent : baseEnd_1001496 < baseStart_1001496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001498 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_1001498 : Nat := 118140960795 + 1001498 * 2 ^ 59
def prefixEnd_1001498 : Nat := 4983230072969 + 3 ^ 40 * 1001498 * 2
def baseEnd_1001498 : Nat := 114277744114806192926489

theorem tailTrace_1001498 : CollatzResearch.WordTrace tailWord_1001498 prefixEnd_1001498 114277744114806192926489 := by
  unfold tailWord_1001498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9131908231437815771535287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24351755283834175390760765 9131908231437815771535287)
  ·
    refine ⟨13697862347156723657302931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9131908231437815771535287 13697862347156723657302931)
    ·
      refine ⟨20546793520735085485954397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13697862347156723657302931 20546793520735085485954397)
      ·
        refine ⟨7705047570275657057232899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20546793520735085485954397 7705047570275657057232899)
        ·
          refine ⟨11557571355413485585849349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7705047570275657057232899 11557571355413485585849349)
          ·
            refine ⟨2167044629140028547346753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11557571355413485585849349 2167044629140028547346753)
            ·
              refine ⟨1625283471855021410510065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167044629140028547346753 1625283471855021410510065)
              ·
                refine ⟨1218962603891266057882549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1625283471855021410510065 1218962603891266057882549)
                ·
                  refine ⟨114277744114806192926489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1218962603891266057882549 114277744114806192926489)
                  ·
                    rfl

theorem cell22_1001498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_1001498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001498 prefixEnd_1001498 := by exact prefixLift 1001498
  have htrace : WordTrace (prefixWord ++ tailWord_1001498) baseStart_1001498 baseEnd_1001498 := by
    simpa [prefixWord, tailWord_1001498, baseEnd_1001498] using wordTrace_append hprefix tailTrace_1001498
  have hstable : (prefixWord ++ tailWord_1001498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001498).length < 2 ^ (prefixWord ++ tailWord_1001498).sum := by decide
  have hdescent : baseEnd_1001498 < baseStart_1001498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001616 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 7]
def baseStart_1001616 : Nat := 118140960795 + 1001616 * 2 ^ 59
def prefixEnd_1001616 : Nat := 4983230072969 + 3 ^ 40 * 1001616 * 2
def baseEnd_1001616 : Nat := 114291208718635201443035

theorem tailTrace_1001616 : CollatzResearch.WordTrace tailWord_1001616 prefixEnd_1001616 114291208718635201443035 := by
  unfold tailWord_1001616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18265968369661884619468351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24354624492882512825957801 18265968369661884619468351)
  ·
    refine ⟨27398952554492826929202527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18265968369661884619468351 27398952554492826929202527)
    ·
      refine ⟨41098428831739240393803791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27398952554492826929202527 41098428831739240393803791)
      ·
        refine ⟨61647643247608860590705687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41098428831739240393803791 61647643247608860590705687)
        ·
          refine ⟨92471464871413290886058531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61647643247608860590705687 92471464871413290886058531)
          ·
            refine ⟨138707197307119936329087797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92471464871413290886058531 138707197307119936329087797)
            ·
              refine ⟨13003799747542494030851981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138707197307119936329087797 13003799747542494030851981)
              ·
                refine ⟨4876424905328435261569493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13003799747542494030851981 4876424905328435261569493)
                ·
                  refine ⟨114291208718635201443035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4876424905328435261569493 114291208718635201443035)
                  ·
                    rfl

theorem cell22_1001616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_1001616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001616 prefixEnd_1001616 := by exact prefixLift 1001616
  have htrace : WordTrace (prefixWord ++ tailWord_1001616) baseStart_1001616 baseEnd_1001616 := by
    simpa [prefixWord, tailWord_1001616, baseEnd_1001616] using wordTrace_append hprefix tailTrace_1001616
  have hstable : (prefixWord ++ tailWord_1001616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001616).length < 2 ^ (prefixWord ++ tailWord_1001616).sum := by decide
  have hdescent : baseEnd_1001616 < baseStart_1001616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001618 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1001618 : Nat := 118140960795 + 1001618 * 2 ^ 59
def prefixEnd_1001618 : Nat := 4983230072969 + 3 ^ 40 * 1001618 * 2
def baseEnd_1001618 : Nat := 342874310796778265779099

theorem tailTrace_1001618 : CollatzResearch.WordTrace tailWord_1001618 prefixEnd_1001618 342874310796778265779099 := by
  unfold tailWord_1001618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133002421329130895127377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24354673123544349053673005 9133002421329130895127377)
  ·
    refine ⟨6849751815996848171345533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9133002421329130895127377 6849751815996848171345533)
    ·
      refine ⟨2568656930998818064254575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6849751815996848171345533 2568656930998818064254575)
      ·
        refine ⟨3852985396498227096381863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568656930998818064254575 3852985396498227096381863)
        ·
          refine ⟨5779478094747340644572795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852985396498227096381863 5779478094747340644572795)
          ·
            refine ⟨8669217142121010966859193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779478094747340644572795 8669217142121010966859193)
            ·
              refine ⟨6501912856590758225144395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8669217142121010966859193 6501912856590758225144395)
              ·
                refine ⟨9752869284886137337716593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501912856590758225144395 9752869284886137337716593)
                ·
                  refine ⟨7314651963664603003287445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9752869284886137337716593 7314651963664603003287445)
                  ·
                    refine ⟨342874310796778265779099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7314651963664603003287445 342874310796778265779099)
                    ·
                      rfl

theorem cell22_1001618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1001618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001618 prefixEnd_1001618 := by exact prefixLift 1001618
  have htrace : WordTrace (prefixWord ++ tailWord_1001618) baseStart_1001618 baseEnd_1001618 := by
    simpa [prefixWord, tailWord_1001618, baseEnd_1001618] using wordTrace_append hprefix tailTrace_1001618
  have hstable : (prefixWord ++ tailWord_1001618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001618).length < 2 ^ (prefixWord ++ tailWord_1001618).sum := by decide
  have hdescent : baseEnd_1001618 < baseStart_1001618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001626 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_1001626 : Nat := 118140960795 + 1001626 * 2 ^ 59
def prefixEnd_1001626 : Nat := 4983230072969 + 3 ^ 40 * 1001626 * 2
def baseEnd_1001626 : Nat := 342877049360268911579075

theorem tailTrace_1001626 : CollatzResearch.WordTrace tailWord_1001626 prefixEnd_1001626 342877049360268911579075 := by
  unfold tailWord_1001626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133075367321885236700183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24354867646191693964533821 9133075367321885236700183)
  ·
    refine ⟨13699613050982827855050275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9133075367321885236700183 13699613050982827855050275)
    ·
      refine ⟨20549419576474241782575413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13699613050982827855050275 20549419576474241782575413)
      ·
        refine ⟨1926508085294460167116445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20549419576474241782575413 1926508085294460167116445)
        ·
          refine ⟨722440531985422562668667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1926508085294460167116445 722440531985422562668667)
          ·
            refine ⟨1083660797978133844003001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722440531985422562668667 1083660797978133844003001)
            ·
              refine ⟨812745598483600383002251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083660797978133844003001 812745598483600383002251)
              ·
                refine ⟨1219118397725400574503377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812745598483600383002251 1219118397725400574503377)
                ·
                  refine ⟨914338798294050430877533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219118397725400574503377 914338798294050430877533)
                  ·
                    refine ⟨342877049360268911579075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914338798294050430877533 342877049360268911579075)
                    ·
                      rfl

theorem cell22_1001626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_1001626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001626 prefixEnd_1001626 := by exact prefixLift 1001626
  have htrace : WordTrace (prefixWord ++ tailWord_1001626) baseStart_1001626 baseEnd_1001626 := by
    simpa [prefixWord, tailWord_1001626, baseEnd_1001626] using wordTrace_append hprefix tailTrace_1001626
  have hstable : (prefixWord ++ tailWord_1001626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001626).length < 2 ^ (prefixWord ++ tailWord_1001626).sum := by decide
  have hdescent : baseEnd_1001626 < baseStart_1001626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001708 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_1001708 : Nat := 118140960795 + 1001708 * 2 ^ 59
def prefixEnd_1001708 : Nat := 4983230072969 + 3 ^ 40 * 1001708 * 2
def baseEnd_1001708 : Nat := 342905119636048031028823

theorem tailTrace_1001708 : CollatzResearch.WordTrace tailWord_1001708 prefixEnd_1001708 342905119636048031028823 := by
  unfold tailWord_1001708
  simp only [CollatzResearch.WordTrace]
  refine ⟨18267646127495234475642889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24356861503326979300857185 18267646127495234475642889)
  ·
    refine ⟨13700734595621425856732167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18267646127495234475642889 13700734595621425856732167)
    ·
      refine ⟨20551101893432138785098251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13700734595621425856732167 20551101893432138785098251)
      ·
        refine ⟨30826652840148208177647377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20551101893432138785098251 30826652840148208177647377)
        ·
          refine ⟨23119989630111156133235533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30826652840148208177647377 23119989630111156133235533)
          ·
            refine ⟨8669996111291683549963325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23119989630111156133235533 8669996111291683549963325)
            ·
              refine ⟨3251248541734381331236247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8669996111291683549963325 3251248541734381331236247)
              ·
                refine ⟨4876872812601571996854371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251248541734381331236247 4876872812601571996854371)
                ·
                  refine ⟨7315309218902357995281557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876872812601571996854371 7315309218902357995281557)
                  ·
                    refine ⟨342905119636048031028823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7315309218902357995281557 342905119636048031028823)
                    ·
                      rfl

theorem cell22_1001708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_1001708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001708 prefixEnd_1001708 := by exact prefixLift 1001708
  have htrace : WordTrace (prefixWord ++ tailWord_1001708) baseStart_1001708 baseEnd_1001708 := by
    simpa [prefixWord, tailWord_1001708, baseEnd_1001708] using wordTrace_append hprefix tailTrace_1001708
  have hstable : (prefixWord ++ tailWord_1001708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001708).length < 2 ^ (prefixWord ++ tailWord_1001708).sum := by decide
  have hdescent : baseEnd_1001708 < baseStart_1001708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001710 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1001710 : Nat := 118140960795 + 1001710 * 2 ^ 59
def prefixEnd_1001710 : Nat := 4983230072969 + 3 ^ 40 * 1001710 * 2
def baseEnd_1001710 : Nat := 342905804276920692478817

theorem tailTrace_1001710 : CollatzResearch.WordTrace tailWord_1001710 prefixEnd_1001710 342905804276920692478817 := by
  unfold tailWord_1001710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4566920650122902911607323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24356910133988815528572389 4566920650122902911607323)
  ·
    refine ⟨6850380975184354367410985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4566920650122902911607323 6850380975184354367410985)
    ·
      refine ⟨5137785731388265775558239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6850380975184354367410985 5137785731388265775558239)
      ·
        refine ⟨7706678597082398663337359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137785731388265775558239 7706678597082398663337359)
        ·
          refine ⟨11560017895623597995006039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7706678597082398663337359 11560017895623597995006039)
          ·
            refine ⟨17340026843435396992509059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11560017895623597995006039 17340026843435396992509059)
            ·
              refine ⟨26010040265153095488763589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17340026843435396992509059 26010040265153095488763589)
              ·
                refine ⟨4876882549716205404143173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26010040265153095488763589 4876882549716205404143173)
                ·
                  refine ⟨914415478071788513276845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4876882549716205404143173 914415478071788513276845)
                  ·
                    refine ⟨342905804276920692478817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914415478071788513276845 342905804276920692478817)
                    ·
                      rfl

theorem cell22_1001710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1001710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001710 prefixEnd_1001710 := by exact prefixLift 1001710
  have htrace : WordTrace (prefixWord ++ tailWord_1001710) baseStart_1001710 baseEnd_1001710 := by
    simpa [prefixWord, tailWord_1001710, baseEnd_1001710] using wordTrace_append hprefix tailTrace_1001710
  have hstable : (prefixWord ++ tailWord_1001710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001710).length < 2 ^ (prefixWord ++ tailWord_1001710).sum := by decide
  have hdescent : baseEnd_1001710 < baseStart_1001710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001714 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_1001714 : Nat := 118140960795 + 1001714 * 2 ^ 59
def prefixEnd_1001714 : Nat := 4983230072969 + 3 ^ 40 * 1001714 * 2
def baseEnd_1001714 : Nat := 342907173558666015378805

theorem tailTrace_1001714 : CollatzResearch.WordTrace tailWord_1001714 prefixEnd_1001714 342907173558666015378805 := by
  unfold tailWord_1001714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133877773242182994001049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24357007395312487984002797 9133877773242182994001049)
  ·
    refine ⟨6850408329931637245500787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9133877773242182994001049 6850408329931637245500787)
    ·
      refine ⟨10275612494897455868251181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850408329931637245500787 10275612494897455868251181)
      ·
        refine ⟨3853354685586545950594193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10275612494897455868251181 3853354685586545950594193)
        ·
          refine ⟨2890016014189909462945645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853354685586545950594193 2890016014189909462945645)
          ·
            refine ⟨1083756005321216048604617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2890016014189909462945645 1083756005321216048604617)
            ·
              refine ⟨812817003990912036453463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083756005321216048604617 812817003990912036453463)
              ·
                refine ⟨1219225505986368054680195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812817003990912036453463 1219225505986368054680195)
                ·
                  refine ⟨1828838258979552082020293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219225505986368054680195 1828838258979552082020293)
                  ·
                    refine ⟨342907173558666015378805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1828838258979552082020293 342907173558666015378805)
                    ·
                      rfl

theorem cell22_1001714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_1001714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001714 prefixEnd_1001714 := by exact prefixLift 1001714
  have htrace : WordTrace (prefixWord ++ tailWord_1001714) baseStart_1001714 baseEnd_1001714 := by
    simpa [prefixWord, tailWord_1001714, baseEnd_1001714] using wordTrace_append hprefix tailTrace_1001714
  have hstable : (prefixWord ++ tailWord_1001714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001714).length < 2 ^ (prefixWord ++ tailWord_1001714).sum := by decide
  have hdescent : baseEnd_1001714 < baseStart_1001714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001755 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 3, 3]
def baseStart_1001755 : Nat := 118140960795 + 1001755 * 2 ^ 59
def prefixEnd_1001755 : Nat := 4983230072969 + 3 ^ 40 * 1001755 * 2
def baseEnd_1001755 : Nat := 342921208696555575103679

theorem tailTrace_1001755 : CollatzResearch.WordTrace tailWord_1001755 prefixEnd_1001755 342921208696555575103679 := by
  unfold tailWord_1001755
  simp only [CollatzResearch.WordTrace]
  refine ⟨36537006485820195978246719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24358004323880130652164479 36537006485820195978246719)
  ·
    refine ⟨54805509728730293967370079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36537006485820195978246719 54805509728730293967370079)
    ·
      refine ⟨82208264593095440951055119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54805509728730293967370079 82208264593095440951055119)
      ·
        refine ⟨123312396889643161426582679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82208264593095440951055119 123312396889643161426582679)
        ·
          refine ⟨184968595334464742139874019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123312396889643161426582679 184968595334464742139874019)
          ·
            refine ⟨277452893001697113209811029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184968595334464742139874019 277452893001697113209811029)
            ·
              refine ⟨3251401089863638045427473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 277452893001697113209811029 3251401089863638045427473)
              ·
                refine ⟨2438550817397728534070605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251401089863638045427473 2438550817397728534070605)
                ·
                  refine ⟨914456556524148200276477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2438550817397728534070605 914456556524148200276477)
                  ·
                    refine ⟨342921208696555575103679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914456556524148200276477 342921208696555575103679)
                    ·
                      rfl

theorem cell22_1001755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 3].length) (baseStart_1001755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001755 prefixEnd_1001755 := by exact prefixLift 1001755
  have htrace : WordTrace (prefixWord ++ tailWord_1001755) baseStart_1001755 baseEnd_1001755 := by
    simpa [prefixWord, tailWord_1001755, baseEnd_1001755] using wordTrace_append hprefix tailTrace_1001755
  have hstable : (prefixWord ++ tailWord_1001755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001755).length < 2 ^ (prefixWord ++ tailWord_1001755).sum := by decide
  have hdescent : baseEnd_1001755 < baseStart_1001755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001774 : List Nat := [4, 1, 3, 3, 2, 1, 8]
def baseStart_1001774 : Nat := 118140960795 + 1001774 * 2 ^ 59
def prefixEnd_1001774 : Nat := 4983230072969 + 3 ^ 40 * 1001774 * 2
def baseEnd_1001774 : Nat := 12701026399438735514023

theorem tailTrace_1001774 : CollatzResearch.WordTrace tailWord_1001774 prefixEnd_1001774 12701026399438735514023 := by
  unfold tailWord_1001774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567212434093920277898547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24358466315167574815458917 4567212434093920277898547)
  ·
    refine ⟨6850818651140880416847821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4567212434093920277898547 6850818651140880416847821)
    ·
      refine ⟨2569056994177830156317933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6850818651140880416847821 2569056994177830156317933)
      ·
        refine ⟨963396372816686308619225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2569056994177830156317933 963396372816686308619225)
        ·
          refine ⟨722547279612514731464419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963396372816686308619225 722547279612514731464419)
          ·
            refine ⟨1083820919418772097196629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722547279612514731464419 1083820919418772097196629)
            ·
              refine ⟨12701026399438735514023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1083820919418772097196629 12701026399438735514023)
              ·
                rfl

theorem cell22_1001774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 8].length) (baseStart_1001774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001774 prefixEnd_1001774 := by exact prefixLift 1001774
  have htrace : WordTrace (prefixWord ++ tailWord_1001774) baseStart_1001774 baseEnd_1001774 := by
    simpa [prefixWord, tailWord_1001774, baseEnd_1001774] using wordTrace_append hprefix tailTrace_1001774
  have hstable : (prefixWord ++ tailWord_1001774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001774).length < 2 ^ (prefixWord ++ tailWord_1001774).sum := by decide
  have hdescent : baseEnd_1001774 < baseStart_1001774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001783 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 4, 5]
def baseStart_1001783 : Nat := 118140960795 + 1001783 * 2 ^ 59
def prefixEnd_1001783 : Nat := 4983230072969 + 3 ^ 40 * 1001783 * 2
def baseEnd_1001783 : Nat := 342930793668772835403593

theorem tailTrace_1001783 : CollatzResearch.WordTrace tailWord_1001783 prefixEnd_1001783 342930793668772835403593 := by
  unfold tailWord_1001783
  simp only [CollatzResearch.WordTrace]
  refine ⟨36538027729718756760266003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24358685153145837840177335 36538027729718756760266003)
  ·
    refine ⟨54807041594578135140399005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36538027729718756760266003 54807041594578135140399005)
    ·
      refine ⟨20552640597966800677649627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54807041594578135140399005 20552640597966800677649627)
      ·
        refine ⟨30828960896950201016474441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20552640597966800677649627 30828960896950201016474441)
        ·
          refine ⟨23121720672712650762355831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30828960896950201016474441 23121720672712650762355831)
          ·
            refine ⟨34682581009068976143533747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23121720672712650762355831 34682581009068976143533747)
            ·
              refine ⟨52023871513603464215300621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34682581009068976143533747 52023871513603464215300621)
              ·
                refine ⟨19508951817601299080737733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52023871513603464215300621 19508951817601299080737733)
                ·
                  refine ⟨3657928465800243577638325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19508951817601299080737733 3657928465800243577638325)
                  ·
                    refine ⟨342930793668772835403593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3657928465800243577638325 342930793668772835403593)
                    ·
                      rfl

theorem cell22_1001783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_1001783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001783 prefixEnd_1001783 := by exact prefixLift 1001783
  have htrace : WordTrace (prefixWord ++ tailWord_1001783) baseStart_1001783 baseEnd_1001783 := by
    simpa [prefixWord, tailWord_1001783, baseEnd_1001783] using wordTrace_append hprefix tailTrace_1001783
  have hstable : (prefixWord ++ tailWord_1001783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001783).length < 2 ^ (prefixWord ++ tailWord_1001783).sum := by decide
  have hdescent : baseEnd_1001783 < baseStart_1001783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001785 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 7]
def baseStart_1001785 : Nat := 118140960795 + 1001785 * 2 ^ 59
def prefixEnd_1001785 : Nat := 4983230072969 + 3 ^ 40 * 1001785 * 2
def baseEnd_1001785 : Nat := 114310492769881832284529

theorem tailTrace_1001785 : CollatzResearch.WordTrace tailWord_1001785 prefixEnd_1001785 114310492769881832284529 := by
  unfold tailWord_1001785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36538100675711511101838809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24358733783807674067892539 36538100675711511101838809)
  ·
    refine ⟨27403575506783633326379107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36538100675711511101838809 27403575506783633326379107)
    ·
      refine ⟨41105363260175449989568661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27403575506783633326379107 41105363260175449989568661)
      ·
        refine ⟨1926813902820724218261031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41105363260175449989568661 1926813902820724218261031)
        ·
          refine ⟨2890220854231086327391547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926813902820724218261031 2890220854231086327391547)
          ·
            refine ⟨4335331281346629491087321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890220854231086327391547 4335331281346629491087321)
            ·
              refine ⟨3251498461009972118315491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4335331281346629491087321 3251498461009972118315491)
              ·
                refine ⟨4877247691514958177473237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251498461009972118315491 4877247691514958177473237)
                ·
                  refine ⟨114310492769881832284529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4877247691514958177473237 114310492769881832284529)
                  ·
                    rfl

theorem cell22_1001785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_1001785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001785 prefixEnd_1001785 := by exact prefixLift 1001785
  have htrace : WordTrace (prefixWord ++ tailWord_1001785) baseStart_1001785 baseEnd_1001785 := by
    simpa [prefixWord, tailWord_1001785, baseEnd_1001785] using wordTrace_append hprefix tailTrace_1001785
  have hstable : (prefixWord ++ tailWord_1001785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001785).length < 2 ^ (prefixWord ++ tailWord_1001785).sum := by decide
  have hdescent : baseEnd_1001785 < baseStart_1001785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001815 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 3, 4]
def baseStart_1001815 : Nat := 118140960795 + 1001815 * 2 ^ 59
def prefixEnd_1001815 : Nat := 4983230072969 + 3 ^ 40 * 1001815 * 2
def baseEnd_1001815 : Nat := 342941747922735418603495

theorem tailTrace_1001815 : CollatzResearch.WordTrace tailWord_1001815 prefixEnd_1001815 342941747922735418603495 := by
  unfold tailWord_1001815
  simp only [CollatzResearch.WordTrace]
  refine ⟨36539194865602826225430899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24359463243735217483620599 36539194865602826225430899)
  ·
    refine ⟨54808792298404239338146349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36539194865602826225430899 54808792298404239338146349)
    ·
      refine ⟨20553297111901589751804881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54808792298404239338146349 20553297111901589751804881)
      ·
        refine ⟨15414972833926192313853661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20553297111901589751804881 15414972833926192313853661)
        ·
          refine ⟨5780614812722322117695123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15414972833926192313853661 5780614812722322117695123)
          ·
            refine ⟨8670922219083483176542685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780614812722322117695123 8670922219083483176542685)
            ·
              refine ⟨3251595832156306191203507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8670922219083483176542685 3251595832156306191203507)
              ·
                refine ⟨4877393748234459286805261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251595832156306191203507 4877393748234459286805261)
                ·
                  refine ⟨1829022655587922232551973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4877393748234459286805261 1829022655587922232551973)
                  ·
                    refine ⟨342941747922735418603495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1829022655587922232551973 342941747922735418603495)
                    ·
                      rfl

theorem cell22_1001815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_1001815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001815 prefixEnd_1001815 := by exact prefixLift 1001815
  have htrace : WordTrace (prefixWord ++ tailWord_1001815) baseStart_1001815 baseEnd_1001815 := by
    simpa [prefixWord, tailWord_1001815, baseEnd_1001815] using wordTrace_append hprefix tailTrace_1001815
  have hstable : (prefixWord ++ tailWord_1001815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001815).length < 2 ^ (prefixWord ++ tailWord_1001815).sum := by decide
  have hdescent : baseEnd_1001815 < baseStart_1001815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001860 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1001860 : Nat := 118140960795 + 1001860 * 2 ^ 59
def prefixEnd_1001860 : Nat := 4983230072969 + 3 ^ 40 * 1001860 * 2
def baseEnd_1001860 : Nat := 342957152342370301228357

theorem tailTrace_1001860 : CollatzResearch.WordTrace tailWord_1001860 prefixEnd_1001860 342957152342370301228357 := by
  unfold tailWord_1001860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18270418075219899455409517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24360557433626532607212689 18270418075219899455409517)
  ·
    refine ⟨6851406778207462295778569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18270418075219899455409517 6851406778207462295778569)
    ·
      refine ⟨5138555083655596721833927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6851406778207462295778569 5138555083655596721833927)
      ·
        refine ⟨7707832625483395082750891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138555083655596721833927 7707832625483395082750891)
        ·
          refine ⟨11561748938225092624126337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7707832625483395082750891 11561748938225092624126337)
          ·
            refine ⟨8671311703668819468094753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11561748938225092624126337 8671311703668819468094753)
            ·
              refine ⟨6503483777751614601071065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8671311703668819468094753 6503483777751614601071065)
              ·
                refine ⟨4877612833313710950803299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6503483777751614601071065 4877612833313710950803299)
                ·
                  refine ⟨7316419249970566426204949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877612833313710950803299 7316419249970566426204949)
                  ·
                    refine ⟨342957152342370301228357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7316419249970566426204949 342957152342370301228357)
                    ·
                      rfl

theorem cell22_1001860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1001860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001860 prefixEnd_1001860 := by exact prefixLift 1001860
  have htrace : WordTrace (prefixWord ++ tailWord_1001860) baseStart_1001860 baseEnd_1001860 := by
    simpa [prefixWord, tailWord_1001860, baseEnd_1001860] using wordTrace_append hprefix tailTrace_1001860
  have hstable : (prefixWord ++ tailWord_1001860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001860).length < 2 ^ (prefixWord ++ tailWord_1001860).sum := by decide
  have hdescent : baseEnd_1001860 < baseStart_1001860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001896 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1001896 : Nat := 118140960795 + 1001896 * 2 ^ 59
def prefixEnd_1001896 : Nat := 4983230072969 + 3 ^ 40 * 1001896 * 2
def baseEnd_1001896 : Nat := 342969475878078207328247

theorem tailTrace_1001896 : CollatzResearch.WordTrace tailWord_1001896 prefixEnd_1001896 342969475878078207328247 := by
  unfold tailWord_1001896
  simp only [CollatzResearch.WordTrace]
  refine ⟨18271074589154688529564771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24361432785539584706086361 18271074589154688529564771)
  ·
    refine ⟨27406611883732032794347157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18271074589154688529564771 27406611883732032794347157)
    ·
      refine ⟨1284684932049939037235023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27406611883732032794347157 1284684932049939037235023)
      ·
        refine ⟨1927027398074908555852535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284684932049939037235023 1927027398074908555852535)
        ·
          refine ⟨2890541097112362833778803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927027398074908555852535 2890541097112362833778803)
          ·
            refine ⟨4335811645668544250668205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890541097112362833778803 4335811645668544250668205)
            ·
              refine ⟨1625929367125704094000577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4335811645668544250668205 1625929367125704094000577)
              ·
                refine ⟨1219447025344278070500433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1625929367125704094000577 1219447025344278070500433)
                ·
                  refine ⟨914585269008208552875325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219447025344278070500433 914585269008208552875325)
                  ·
                    refine ⟨342969475878078207328247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914585269008208552875325 342969475878078207328247)
                    ·
                      rfl

theorem cell22_1001896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1001896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001896 prefixEnd_1001896 := by exact prefixLift 1001896
  have htrace : WordTrace (prefixWord ++ tailWord_1001896) baseStart_1001896 baseEnd_1001896 := by
    simpa [prefixWord, tailWord_1001896, baseEnd_1001896] using wordTrace_append hprefix tailTrace_1001896
  have hstable : (prefixWord ++ tailWord_1001896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001896).length < 2 ^ (prefixWord ++ tailWord_1001896).sum := by decide
  have hdescent : baseEnd_1001896 < baseStart_1001896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001941 : List Nat := [1, 3, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_1001941 : Nat := 118140960795 + 1001941 * 2 ^ 59
def prefixEnd_1001941 : Nat := 4983230072969 + 3 ^ 40 * 1001941 * 2
def baseEnd_1001941 : Nat := 342984880297713089953109

theorem tailTrace_1001941 : CollatzResearch.WordTrace tailWord_1001941 prefixEnd_1001941 342984880297713089953109 := by
  unfold tailWord_1001941
  simp only [CollatzResearch.WordTrace]
  refine ⟨36543790463146349744517677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24362526975430899829678451 36543790463146349744517677)
  ·
    refine ⟨13703921423679881154194129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36543790463146349744517677 13703921423679881154194129)
    ·
      refine ⟨10277941067759910865645597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13703921423679881154194129 10277941067759910865645597)
      ·
        refine ⟨3854227900409966574617099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10277941067759910865645597 3854227900409966574617099)
        ·
          refine ⟨5781341850614949861925649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854227900409966574617099 5781341850614949861925649)
          ·
            refine ⟨4336006387961212396444237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781341850614949861925649 4336006387961212396444237)
            ·
              refine ⟨1626002395485454648666589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4336006387961212396444237 1626002395485454648666589)
              ·
                refine ⟨609750898307045493249971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1626002395485454648666589 609750898307045493249971)
                ·
                  refine ⟨914626347460568239874957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609750898307045493249971 914626347460568239874957)
                  ·
                    refine ⟨342984880297713089953109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914626347460568239874957 342984880297713089953109)
                    ·
                      rfl

theorem cell22_1001941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_1001941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1001941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1001941 prefixEnd_1001941 := by exact prefixLift 1001941
  have htrace : WordTrace (prefixWord ++ tailWord_1001941) baseStart_1001941 baseEnd_1001941 := by
    simpa [prefixWord, tailWord_1001941, baseEnd_1001941] using wordTrace_append hprefix tailTrace_1001941
  have hstable : (prefixWord ++ tailWord_1001941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001941).length < 2 ^ (prefixWord ++ tailWord_1001941).sum := by decide
  have hdescent : baseEnd_1001941 < baseStart_1001941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002016 : List Nat := [2, 1, 1, 6, 2, 1, 1, 4, 4]
def baseStart_1002016 : Nat := 118140960795 + 1002016 * 2 ^ 59
def prefixEnd_1002016 : Nat := 4983230072969 + 3 ^ 40 * 1002016 * 2
def baseEnd_1002016 : Nat := 114336851443479298109293

theorem tailTrace_1002016 : CollatzResearch.WordTrace tailWord_1002016 prefixEnd_1002016 114336851443479298109293 := by
  unfold tailWord_1002016
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273262968937318776748951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24364350625249758368998601 18273262968937318776748951)
  ·
    refine ⟨27409894453405978165123427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18273262968937318776748951 27409894453405978165123427)
    ·
      refine ⟨41114841680108967247685141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27409894453405978165123427 41114841680108967247685141)
      ·
        refine ⟨1927258203755107839735241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41114841680108967247685141 1927258203755107839735241)
        ·
          refine ⟨1445443652816330879801431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1927258203755107839735241 1445443652816330879801431)
          ·
            refine ⟨2168165479224496319702147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445443652816330879801431 2168165479224496319702147)
            ·
              refine ⟨3252248218836744479553221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168165479224496319702147 3252248218836744479553221)
              ·
                refine ⟨609796541031889589916229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3252248218836744479553221 609796541031889589916229)
                ·
                  refine ⟨114336851443479298109293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609796541031889589916229 114336851443479298109293)
                  ·
                    rfl

theorem cell22_1002016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 4].length) (baseStart_1002016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002016 prefixEnd_1002016 := by exact prefixLift 1002016
  have htrace : WordTrace (prefixWord ++ tailWord_1002016) baseStart_1002016 baseEnd_1002016 := by
    simpa [prefixWord, tailWord_1002016, baseEnd_1002016] using wordTrace_append hprefix tailTrace_1002016
  have hstable : (prefixWord ++ tailWord_1002016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002016).length < 2 ^ (prefixWord ++ tailWord_1002016).sum := by decide
  have hdescent : baseEnd_1002016 < baseStart_1002016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002044 : List Nat := [2, 2, 2, 2, 3, 2, 3, 6]
def baseStart_1002044 : Nat := 118140960795 + 1002044 * 2 ^ 59
def prefixEnd_1002044 : Nat := 4983230072969 + 3 ^ 40 * 1002044 * 2
def baseEnd_1002044 : Nat := 38113348811406128291977

theorem tailTrace_1002044 : CollatzResearch.WordTrace tailWord_1002044 prefixEnd_1002044 38113348811406128291977 := by
  unfold tailWord_1002044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273773590886599167758593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24365031454515465557011457 18273773590886599167758593)
  ·
    refine ⟨13705330193164949375818945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18273773590886599167758593 13705330193164949375818945)
    ·
      refine ⟨10278997644873712031864209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13705330193164949375818945 10278997644873712031864209)
      ·
        refine ⟨7709248233655284023898157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10278997644873712031864209 7709248233655284023898157)
        ·
          refine ⟨2890968087620731508961809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7709248233655284023898157 2890968087620731508961809)
          ·
            refine ⟨2168226065715548631721357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2890968087620731508961809 2168226065715548631721357)
            ·
              refine ⟨813084774643330736895509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2168226065715548631721357 813084774643330736895509)
              ·
                refine ⟨38113348811406128291977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 813084774643330736895509 38113348811406128291977)
                ·
                  rfl

theorem cell22_1002044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 6].length) (baseStart_1002044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002044 prefixEnd_1002044 := by exact prefixLift 1002044
  have htrace : WordTrace (prefixWord ++ tailWord_1002044) baseStart_1002044 baseEnd_1002044 := by
    simpa [prefixWord, tailWord_1002044, baseEnd_1002044] using wordTrace_append hprefix tailTrace_1002044
  have hstable : (prefixWord ++ tailWord_1002044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002044).length < 2 ^ (prefixWord ++ tailWord_1002044).sum := by decide
  have hdescent : baseEnd_1002044 < baseStart_1002044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002046 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1002046 : Nat := 118140960795 + 1002046 * 2 ^ 59
def prefixEnd_1002046 : Nat := 4983230072969 + 3 ^ 40 * 1002046 * 2
def baseEnd_1002046 : Nat := 343020823943527816077787

theorem tailTrace_1002046 : CollatzResearch.WordTrace tailWord_1002046 prefixEnd_1002046 343020823943527816077787 := by
  unfold tailWord_1002046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568452515970744084636249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24365080085177301784726661 4568452515970744084636249)
  ·
    refine ⟨3426339386978058063477187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4568452515970744084636249 3426339386978058063477187)
    ·
      refine ⟨5139509080467087095215781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426339386978058063477187 5139509080467087095215781)
      ·
        refine ⟨963657952587578830352959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5139509080467087095215781 963657952587578830352959)
        ·
          refine ⟨1445486928881368245529439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963657952587578830352959 1445486928881368245529439)
          ·
            refine ⟨2168230393322052368294159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445486928881368245529439 2168230393322052368294159)
            ·
              refine ⟨3252345589983078552441239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168230393322052368294159 3252345589983078552441239)
              ·
                refine ⟨4878518384974617828661859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252345589983078552441239 4878518384974617828661859)
                ·
                  refine ⟨7317777577461926742992789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878518384974617828661859 7317777577461926742992789)
                  ·
                    refine ⟨343020823943527816077787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7317777577461926742992789 343020823943527816077787)
                    ·
                      rfl

theorem cell22_1002046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1002046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002046 prefixEnd_1002046 := by exact prefixLift 1002046
  have htrace : WordTrace (prefixWord ++ tailWord_1002046) baseStart_1002046 baseEnd_1002046 := by
    simpa [prefixWord, tailWord_1002046, baseEnd_1002046] using wordTrace_append hprefix tailTrace_1002046
  have hstable : (prefixWord ++ tailWord_1002046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002046).length < 2 ^ (prefixWord ++ tailWord_1002046).sum := by decide
  have hdescent : baseEnd_1002046 < baseStart_1002046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002052 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1002052 : Nat := 118140960795 + 1002052 * 2 ^ 59
def prefixEnd_1002052 : Nat := 4983230072969 + 3 ^ 40 * 1002052 * 2
def baseEnd_1002052 : Nat := 343022877866145800427769

theorem tailTrace_1002052 : CollatzResearch.WordTrace tailWord_1002052 prefixEnd_1002052 343022877866145800427769 := by
  unfold tailWord_1002052
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273919482872107850904205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24365225977162810467872273 18273919482872107850904205)
  ·
    refine ⟨6852719806077040444089077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18273919482872107850904205 6852719806077040444089077)
    ·
      refine ⟨642442481819722541633351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6852719806077040444089077 642442481819722541633351)
      ·
        refine ⟨963663722729583812450027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642442481819722541633351 963663722729583812450027)
        ·
          refine ⟨1445495584094375718675041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963663722729583812450027 1445495584094375718675041)
          ·
            refine ⟨1084121688070781789006281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445495584094375718675041 1084121688070781789006281)
            ·
              refine ⟨813091266053086341754711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084121688070781789006281 813091266053086341754711)
              ·
                refine ⟨1219636899079629512632067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813091266053086341754711 1219636899079629512632067)
                ·
                  refine ⟨1829455348619444268948101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219636899079629512632067 1829455348619444268948101)
                  ·
                    refine ⟨343022877866145800427769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1829455348619444268948101 343022877866145800427769)
                    ·
                      rfl

theorem cell22_1002052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1002052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002052 prefixEnd_1002052 := by exact prefixLift 1002052
  have htrace : WordTrace (prefixWord ++ tailWord_1002052) baseStart_1002052 baseEnd_1002052 := by
    simpa [prefixWord, tailWord_1002052, baseEnd_1002052] using wordTrace_append hprefix tailTrace_1002052
  have hstable : (prefixWord ++ tailWord_1002052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002052).length < 2 ^ (prefixWord ++ tailWord_1002052).sum := by decide
  have hdescent : baseEnd_1002052 < baseStart_1002052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002119 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1002119 : Nat := 118140960795 + 1002119 * 2 ^ 59
def prefixEnd_1002119 : Nat := 4983230072969 + 3 ^ 40 * 1002119 * 2
def baseEnd_1002119 : Nat := 343045813335379959002563

theorem tailTrace_1002119 : CollatzResearch.WordTrace tailWord_1002119 prefixEnd_1002119 343045813335379959002563 := by
  unfold tailWord_1002119
  simp only [CollatzResearch.WordTrace]
  refine ⟨36550282656501486144497411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24366855104334324096331607 36550282656501486144497411)
  ·
    refine ⟨54825423984752229216746117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36550282656501486144497411 54825423984752229216746117)
    ·
      refine ⟨10279766997141042978139897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54825423984752229216746117 10279766997141042978139897)
      ·
        refine ⟨7709825247855782233604923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10279766997141042978139897 7709825247855782233604923)
        ·
          refine ⟨11564737871783673350407385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709825247855782233604923 11564737871783673350407385)
          ·
            refine ⟨8673553403837755012805539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11564737871783673350407385 8673553403837755012805539)
            ·
              refine ⟨13010330105756632519208309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673553403837755012805539 13010330105756632519208309)
              ·
                refine ⟨1219718447414684298675779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13010330105756632519208309 1219718447414684298675779)
                ·
                  refine ⟨1829577671122026448013669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219718447414684298675779 1829577671122026448013669)
                  ·
                    refine ⟨343045813335379959002563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1829577671122026448013669 343045813335379959002563)
                    ·
                      rfl

theorem cell22_1002119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1002119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002119 prefixEnd_1002119 := by exact prefixLift 1002119
  have htrace : WordTrace (prefixWord ++ tailWord_1002119) baseStart_1002119 baseEnd_1002119 := by
    simpa [prefixWord, tailWord_1002119, baseEnd_1002119] using wordTrace_append hprefix tailTrace_1002119
  have hstable : (prefixWord ++ tailWord_1002119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002119).length < 2 ^ (prefixWord ++ tailWord_1002119).sum := by decide
  have hdescent : baseEnd_1002119 < baseStart_1002119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002147 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 1, 6]
def baseStart_1002147 : Nat := 118140960795 + 1002147 * 2 ^ 59
def prefixEnd_1002147 : Nat := 4983230072969 + 3 ^ 40 * 1002147 * 2
def baseEnd_1002147 : Nat := 343055398307597219302477

theorem tailTrace_1002147 : CollatzResearch.WordTrace tailWord_1002147 prefixEnd_1002147 343055398307597219302477 := by
  unfold tailWord_1002147
  simp only [CollatzResearch.WordTrace]
  refine ⟨36551303900400046926516695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24367535933600031284344463 36551303900400046926516695)
  ·
    refine ⟨54826955850600070389775043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36551303900400046926516695 54826955850600070389775043)
    ·
      refine ⟨82240433775900105584662565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54826955850600070389775043 82240433775900105584662565)
      ·
        refine ⟨15420081332981269797124231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82240433775900105584662565 15420081332981269797124231)
        ·
          refine ⟨23130121999471904695686347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15420081332981269797124231 23130121999471904695686347)
          ·
            refine ⟨34695182999207857043529521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23130121999471904695686347 34695182999207857043529521)
            ·
              refine ⟨26021387249405892782647141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34695182999207857043529521 26021387249405892782647141)
              ·
                refine ⟨4879010109263604896746339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26021387249405892782647141 4879010109263604896746339)
                ·
                  refine ⟨7318515163895407345119509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879010109263604896746339 7318515163895407345119509)
                  ·
                    refine ⟨343055398307597219302477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7318515163895407345119509 343055398307597219302477)
                    ·
                      rfl

theorem cell22_1002147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_1002147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002147 prefixEnd_1002147 := by exact prefixLift 1002147
  have htrace : WordTrace (prefixWord ++ tailWord_1002147) baseStart_1002147 baseEnd_1002147 := by
    simpa [prefixWord, tailWord_1002147, baseEnd_1002147] using wordTrace_append hprefix tailTrace_1002147
  have hstable : (prefixWord ++ tailWord_1002147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002147).length < 2 ^ (prefixWord ++ tailWord_1002147).sum := by decide
  have hdescent : baseEnd_1002147 < baseStart_1002147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002211 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 5, 3]
def baseStart_1002211 : Nat := 118140960795 + 1002211 * 2 ^ 59
def prefixEnd_1002211 : Nat := 4983230072969 + 3 ^ 40 * 1002211 * 2
def baseEnd_1002211 : Nat := 343077306815522385702281

theorem tailTrace_1002211 : CollatzResearch.WordTrace tailWord_1002211 prefixEnd_1002211 343077306815522385702281 := by
  unfold tailWord_1002211
  simp only [CollatzResearch.WordTrace]
  refine ⟨36553638172168185856846487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24369092114778790571230991 36553638172168185856846487)
  ·
    refine ⟨54830457258252278785269731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36553638172168185856846487 54830457258252278785269731)
    ·
      refine ⟨82245685887378418177904597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54830457258252278785269731 82245685887378418177904597)
      ·
        refine ⟨1927633262985431676044639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 82245685887378418177904597 1927633262985431676044639)
        ·
          refine ⟨2891449894478147514066959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927633262985431676044639 2891449894478147514066959)
          ·
            refine ⟨4337174841717221271100439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891449894478147514066959 4337174841717221271100439)
            ·
              refine ⟨6505762262575831906650659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337174841717221271100439 6505762262575831906650659)
              ·
                refine ⟨9758643393863747859975989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6505762262575831906650659 9758643393863747859975989)
                ·
                  refine ⟨914872818174726361872749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9758643393863747859975989 914872818174726361872749)
                  ·
                    refine ⟨343077306815522385702281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914872818174726361872749 343077306815522385702281)
                    ·
                      rfl

theorem cell22_1002211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 3].length) (baseStart_1002211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002211 prefixEnd_1002211 := by exact prefixLift 1002211
  have htrace : WordTrace (prefixWord ++ tailWord_1002211) baseStart_1002211 baseEnd_1002211 := by
    simpa [prefixWord, tailWord_1002211, baseEnd_1002211] using wordTrace_append hprefix tailTrace_1002211
  have hstable : (prefixWord ++ tailWord_1002211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002211).length < 2 ^ (prefixWord ++ tailWord_1002211).sum := by decide
  have hdescent : baseEnd_1002211 < baseStart_1002211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002271 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 1, 4]
def baseStart_1002271 : Nat := 118140960795 + 1002271 * 2 ^ 59
def prefixEnd_1002271 : Nat := 4983230072969 + 3 ^ 40 * 1002271 * 2
def baseEnd_1002271 : Nat := 343097846041702229202097

theorem tailTrace_1002271 : CollatzResearch.WordTrace tailWord_1002271 prefixEnd_1002271 343097846041702229202097 := by
  unfold tailWord_1002271
  simp only [CollatzResearch.WordTrace]
  refine ⟨36555826551950816104030667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24370551034633877402687111 36555826551950816104030667)
  ·
    refine ⟨54833739827926224156046001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36555826551950816104030667 54833739827926224156046001)
    ·
      refine ⟨41125304870944668117034501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54833739827926224156046001 41125304870944668117034501)
      ·
        refine ⟨7710994663302125271943969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41125304870944668117034501 7710994663302125271943969)
        ·
          refine ⟨5783245997476593953957977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7710994663302125271943969 5783245997476593953957977)
          ·
            refine ⟨4337434498107445465468483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5783245997476593953957977 4337434498107445465468483)
            ·
              refine ⟨6506151747161168198202725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337434498107445465468483 6506151747161168198202725)
              ·
                refine ⟨1219903452592719037163011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6506151747161168198202725 1219903452592719037163011)
                ·
                  refine ⟨1829855178889078555744517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219903452592719037163011 1829855178889078555744517)
                  ·
                    refine ⟨343097846041702229202097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1829855178889078555744517 343097846041702229202097)
                    ·
                      rfl

theorem cell22_1002271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_1002271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002271 prefixEnd_1002271 := by exact prefixLift 1002271
  have htrace : WordTrace (prefixWord ++ tailWord_1002271) baseStart_1002271 baseEnd_1002271 := by
    simpa [prefixWord, tailWord_1002271, baseEnd_1002271] using wordTrace_append hprefix tailTrace_1002271
  have hstable : (prefixWord ++ tailWord_1002271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002271).length < 2 ^ (prefixWord ++ tailWord_1002271).sum := by decide
  have hdescent : baseEnd_1002271 < baseStart_1002271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002284 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_1002284 : Nat := 118140960795 + 1002284 * 2 ^ 59
def prefixEnd_1002284 : Nat := 4983230072969 + 3 ^ 40 * 1002284 * 2
def baseEnd_1002284 : Nat := 343102296207374528627057

theorem tailTrace_1002284 : CollatzResearch.WordTrace tailWord_1002284 prefixEnd_1002284 343102296207374528627057 := by
  unfold tailWord_1002284
  simp only [CollatzResearch.WordTrace]
  refine ⟨18278150350451859662126953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24370867133935812882835937 18278150350451859662126953)
  ·
    refine ⟨13708612762838894746595215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18278150350451859662126953 13708612762838894746595215)
    ·
      refine ⟨20562919144258342119892823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13708612762838894746595215 20562919144258342119892823)
      ·
        refine ⟨30844378716387513179839235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20562919144258342119892823 30844378716387513179839235)
        ·
          refine ⟨46266568074581269769758853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30844378716387513179839235 46266568074581269769758853)
          ·
            refine ⟨8674981513983988081829785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46266568074581269769758853 8674981513983988081829785)
            ·
              refine ⟨6506236135487991061372339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8674981513983988081829785 6506236135487991061372339)
              ·
                refine ⟨9759354203231986592058509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506236135487991061372339 9759354203231986592058509)
                ·
                  refine ⟨3659757826211994972021941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9759354203231986592058509 3659757826211994972021941)
                  ·
                    refine ⟨343102296207374528627057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3659757826211994972021941 343102296207374528627057)
                    ·
                      rfl

theorem cell22_1002284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_1002284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002284 prefixEnd_1002284 := by exact prefixLift 1002284
  have htrace : WordTrace (prefixWord ++ tailWord_1002284) baseStart_1002284 baseEnd_1002284 := by
    simpa [prefixWord, tailWord_1002284, baseEnd_1002284] using wordTrace_append hprefix tailTrace_1002284
  have hstable : (prefixWord ++ tailWord_1002284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002284).length < 2 ^ (prefixWord ++ tailWord_1002284).sum := by decide
  have hdescent : baseEnd_1002284 < baseStart_1002284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002359 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 7]
def baseStart_1002359 : Nat := 118140960795 + 1002359 * 2 ^ 59
def prefixEnd_1002359 : Nat := 4983230072969 + 3 ^ 40 * 1002359 * 2
def baseEnd_1002359 : Nat := 114375990080033111000609

theorem tailTrace_1002359 : CollatzResearch.WordTrace tailWord_1002359 prefixEnd_1002359 114375990080033111000609 := by
  unfold tailWord_1002359
  simp only [CollatzResearch.WordTrace]
  refine ⟨36559036175632007133234131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24372690783754671422156087 36559036175632007133234131)
  ·
    refine ⟨54838554263448010699851197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36559036175632007133234131 54838554263448010699851197)
    ·
      refine ⟨20564457848793004012444199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54838554263448010699851197 20564457848793004012444199)
      ·
        refine ⟨30846686773189506018666299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20564457848793004012444199 30846686773189506018666299)
        ·
          refine ⟨46270030159784259027999449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30846686773189506018666299 46270030159784259027999449)
          ·
            refine ⟨34702522619838194270999587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46270030159784259027999449 34702522619838194270999587)
            ·
              refine ⟨52053783929757291406499381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34702522619838194270999587 52053783929757291406499381)
              ·
                refine ⟨4880042243414746069359317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52053783929757291406499381 4880042243414746069359317)
                ·
                  refine ⟨114375990080033111000609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4880042243414746069359317 114375990080033111000609)
                  ·
                    rfl

theorem cell22_1002359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 7].length) (baseStart_1002359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002359 prefixEnd_1002359 := by exact prefixLift 1002359
  have htrace : WordTrace (prefixWord ++ tailWord_1002359) baseStart_1002359 baseEnd_1002359 := by
    simpa [prefixWord, tailWord_1002359, baseEnd_1002359] using wordTrace_append hprefix tailTrace_1002359
  have hstable : (prefixWord ++ tailWord_1002359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002359).length < 2 ^ (prefixWord ++ tailWord_1002359).sum := by decide
  have hdescent : baseEnd_1002359 < baseStart_1002359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002440 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1002440 : Nat := 118140960795 + 1002440 * 2 ^ 59
def prefixEnd_1002440 : Nat := 4983230072969 + 3 ^ 40 * 1002440 * 2
def baseEnd_1002440 : Nat := 343155698195442121726579

theorem tailTrace_1002440 : CollatzResearch.WordTrace tailWord_1002440 prefixEnd_1002440 343155698195442121726579 := by
  unfold tailWord_1002440
  simp only [CollatzResearch.WordTrace]
  refine ⟨18280995244169278983466387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24374660325559038644621849 18280995244169278983466387)
  ·
    refine ⟨27421492866253918475199581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18280995244169278983466387 27421492866253918475199581)
    ·
      refine ⟨10283059824845219428199843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27421492866253918475199581 10283059824845219428199843)
      ·
        refine ⟨15424589737267829142299765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283059824845219428199843 15424589737267829142299765)
        ·
          refine ⟨1446055287868858982090603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15424589737267829142299765 1446055287868858982090603)
          ·
            refine ⟨2169082931803288473135905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446055287868858982090603 2169082931803288473135905)
            ·
              refine ⟨1626812198852466354851929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169082931803288473135905 1626812198852466354851929)
              ·
                refine ⟨1220109149139349766138947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626812198852466354851929 1220109149139349766138947)
                ·
                  refine ⟨1830163723709024649208421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220109149139349766138947 1830163723709024649208421)
                  ·
                    refine ⟨343155698195442121726579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830163723709024649208421 343155698195442121726579)
                    ·
                      rfl

theorem cell22_1002440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1002440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002440 prefixEnd_1002440 := by exact prefixLift 1002440
  have htrace : WordTrace (prefixWord ++ tailWord_1002440) baseStart_1002440 baseEnd_1002440 := by
    simpa [prefixWord, tailWord_1002440, baseEnd_1002440] using wordTrace_append hprefix tailTrace_1002440
  have hstable : (prefixWord ++ tailWord_1002440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002440).length < 2 ^ (prefixWord ++ tailWord_1002440).sum := by decide
  have hdescent : baseEnd_1002440 < baseStart_1002440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002515 : List Nat := [1, 1, 1, 2, 1, 4, 1, 7, 1, 3]
def baseStart_1002515 : Nat := 118140960795 + 1002515 * 2 ^ 59
def prefixEnd_1002515 : Nat := 4983230072969 + 3 ^ 40 * 1002515 * 2
def baseEnd_1002515 : Nat := 343181372228166926101349

theorem tailTrace_1002515 : CollatzResearch.WordTrace tailWord_1002515 prefixEnd_1002515 343181372228166926101349 := by
  unfold tailWord_1002515
  simp only [CollatzResearch.WordTrace]
  refine ⟨36564725963066845775912999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24376483975377897183941999 36564725963066845775912999)
  ·
    refine ⟨54847088944600268663869499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36564725963066845775912999 54847088944600268663869499)
    ·
      refine ⟨82270633416900402995804249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54847088944600268663869499 82270633416900402995804249)
      ·
        refine ⟨61702975062675302246853187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82270633416900402995804249 61702975062675302246853187)
        ·
          refine ⟨92554462594012953370279781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61702975062675302246853187 92554462594012953370279781)
          ·
            refine ⟨17353961736377428756927459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92554462594012953370279781 17353961736377428756927459)
            ·
              refine ⟨26030942604566143135391189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17353961736377428756927459 26030942604566143135391189)
              ·
                refine ⟨610100217294518979735731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26030942604566143135391189 610100217294518979735731)
                ·
                  refine ⟨915150325941778469603597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610100217294518979735731 915150325941778469603597)
                  ·
                    refine ⟨343181372228166926101349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 915150325941778469603597 343181372228166926101349)
                    ·
                      rfl

theorem cell22_1002515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 3].length) (baseStart_1002515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002515 prefixEnd_1002515 := by exact prefixLift 1002515
  have htrace : WordTrace (prefixWord ++ tailWord_1002515) baseStart_1002515 baseEnd_1002515 := by
    simpa [prefixWord, tailWord_1002515, baseEnd_1002515] using wordTrace_append hprefix tailTrace_1002515
  have hstable : (prefixWord ++ tailWord_1002515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002515).length < 2 ^ (prefixWord ++ tailWord_1002515).sum := by decide
  have hdescent : baseEnd_1002515 < baseStart_1002515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002566 : List Nat := [6, 1, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1002566 : Nat := 118140960795 + 1002566 * 2 ^ 59
def prefixEnd_1002566 : Nat := 4983230072969 + 3 ^ 40 * 1002566 * 2
def baseEnd_1002566 : Nat := 343198830570419793076193

theorem tailTrace_1002566 : CollatzResearch.WordTrace tailWord_1002566 prefixEnd_1002566 343198830570419793076193 := by
  unfold tailWord_1002566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142705815183815046438111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24377724057254720990679701 1142705815183815046438111)
  ·
    refine ⟨1714058722775722569657167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142705815183815046438111 1714058722775722569657167)
    ·
      refine ⟨2571088084163583854485751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714058722775722569657167 2571088084163583854485751)
      ·
        refine ⟨3856632126245375781728627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571088084163583854485751 3856632126245375781728627)
        ·
          refine ⟨5784948189368063672592941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856632126245375781728627 5784948189368063672592941)
          ·
            refine ⟨2169355571013023877222353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5784948189368063672592941 2169355571013023877222353)
            ·
              refine ⟨1627016678259767907916765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169355571013023877222353 1627016678259767907916765)
              ·
                refine ⟨610131254347412965468787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1627016678259767907916765 610131254347412965468787)
                ·
                  refine ⟨915196881521119448203181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610131254347412965468787 915196881521119448203181)
                  ·
                    refine ⟨343198830570419793076193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 915196881521119448203181 343198830570419793076193)
                    ·
                      rfl

theorem cell22_1002566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1002566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002566 prefixEnd_1002566 := by exact prefixLift 1002566
  have htrace : WordTrace (prefixWord ++ tailWord_1002566) baseStart_1002566 baseEnd_1002566 := by
    simpa [prefixWord, tailWord_1002566, baseEnd_1002566] using wordTrace_append hprefix tailTrace_1002566
  have hstable : (prefixWord ++ tailWord_1002566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002566).length < 2 ^ (prefixWord ++ tailWord_1002566).sum := by decide
  have hdescent : baseEnd_1002566 < baseStart_1002566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002605 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_1002605 : Nat := 118140960795 + 1002605 * 2 ^ 59
def prefixEnd_1002605 : Nat := 4983230072969 + 3 ^ 40 * 1002605 * 2
def baseEnd_1002605 : Nat := 343212181067436691351073

theorem tailTrace_1002605 : CollatzResearch.WordTrace tailWord_1002605 prefixEnd_1002605 343212181067436691351073 := by
  unfold tailWord_1002605
  simp only [CollatzResearch.WordTrace]
  refine ⟨36568008532740791146689269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24378672355160527431126179 36568008532740791146689269)
  ·
    refine ⟨3428250799944449170002119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36568008532740791146689269 3428250799944449170002119)
    ·
      refine ⟨5142376199916673755003179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3428250799944449170002119 5142376199916673755003179)
      ·
        refine ⟨7713564299875010632504769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142376199916673755003179 7713564299875010632504769)
        ·
          refine ⟨5785173224906257974378577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7713564299875010632504769 5785173224906257974378577)
          ·
            refine ⟨4338879918679693480783933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5785173224906257974378577 4338879918679693480783933)
            ·
              refine ⟨1627079969504885055293975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4338879918679693480783933 1627079969504885055293975)
              ·
                refine ⟨2440619954257327582940963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627079969504885055293975 2440619954257327582940963)
                ·
                  refine ⟨3660929931385991374411445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440619954257327582940963 3660929931385991374411445)
                  ·
                    refine ⟨343212181067436691351073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3660929931385991374411445 343212181067436691351073)
                    ·
                      rfl

theorem cell22_1002605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_1002605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002605 prefixEnd_1002605 := by exact prefixLift 1002605
  have htrace : WordTrace (prefixWord ++ tailWord_1002605) baseStart_1002605 baseEnd_1002605 := by
    simpa [prefixWord, tailWord_1002605, baseEnd_1002605] using wordTrace_append hprefix tailTrace_1002605
  have hstable : (prefixWord ++ tailWord_1002605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002605).length < 2 ^ (prefixWord ++ tailWord_1002605).sum := by decide
  have hdescent : baseEnd_1002605 < baseStart_1002605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002787 : List Nat := [1, 1, 1, 4, 2, 5, 2, 6]
def baseStart_1002787 : Nat := 118140960795 + 1002787 * 2 ^ 59
def prefixEnd_1002787 : Nat := 4983230072969 + 3 ^ 40 * 1002787 * 2
def baseEnd_1002787 : Nat := 38141609265205431477835

theorem tailTrace_1002787 : CollatzResearch.WordTrace tailWord_1002787 prefixEnd_1002787 38141609265205431477835 := by
  unfold tailWord_1002787
  simp only [CollatzResearch.WordTrace]
  refine ⟨36574646618081436229814615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24383097745387624153209743 36574646618081436229814615)
  ·
    refine ⟨54861969927122154344721923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36574646618081436229814615 54861969927122154344721923)
    ·
      refine ⟨82292954890683231517082885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54861969927122154344721923 82292954890683231517082885)
      ·
        refine ⟨15429929042003105909453041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82292954890683231517082885 15429929042003105909453041)
        ·
          refine ⟨11572446781502329432089781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15429929042003105909453041 11572446781502329432089781)
          ·
            refine ⟨1084916885765843384258417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11572446781502329432089781 1084916885765843384258417)
            ·
              refine ⟨813687664324382538193813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084916885765843384258417 813687664324382538193813)
              ·
                refine ⟨38141609265205431477835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 813687664324382538193813 38141609265205431477835)
                ·
                  rfl

theorem cell22_1002787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 6].length) (baseStart_1002787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002787 prefixEnd_1002787 := by exact prefixLift 1002787
  have htrace : WordTrace (prefixWord ++ tailWord_1002787) baseStart_1002787 baseEnd_1002787 := by
    simpa [prefixWord, tailWord_1002787, baseEnd_1002787] using wordTrace_append hprefix tailTrace_1002787
  have hstable : (prefixWord ++ tailWord_1002787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002787).length < 2 ^ (prefixWord ++ tailWord_1002787).sum := by decide
  have hdescent : baseEnd_1002787 < baseStart_1002787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002806 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1002806 : Nat := 118140960795 + 1002806 * 2 ^ 59
def prefixEnd_1002806 : Nat := 4983230072969 + 3 ^ 40 * 1002806 * 2
def baseEnd_1002806 : Nat := 343280987475139167075457

theorem tailTrace_1002806 : CollatzResearch.WordTrace tailWord_1002806 prefixEnd_1002806 343280987475139167075457 := by
  unfold tailWord_1002806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285958725313287654672267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24383559736675068316504181 2285958725313287654672267)
  ·
    refine ⟨3428938087969931482008401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2285958725313287654672267 3428938087969931482008401)
    ·
      refine ⟨2571703565977448611506301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3428938087969931482008401 2571703565977448611506301)
      ·
        refine ⟨964388837241543229314863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2571703565977448611506301 964388837241543229314863)
        ·
          refine ⟨1446583255862314843972295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964388837241543229314863 1446583255862314843972295)
          ·
            refine ⟨2169874883793472265958443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446583255862314843972295 2169874883793472265958443)
            ·
              refine ⟨3254812325690208398937665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169874883793472265958443 3254812325690208398937665)
              ·
                refine ⟨2441109244267656299203249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3254812325690208398937665 2441109244267656299203249)
                ·
                  refine ⟨1830831933200742224402437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2441109244267656299203249 1830831933200742224402437)
                  ·
                    refine ⟨343280987475139167075457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830831933200742224402437 343280987475139167075457)
                    ·
                      rfl

theorem cell22_1002806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1002806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002806 prefixEnd_1002806 := by exact prefixLift 1002806
  have htrace : WordTrace (prefixWord ++ tailWord_1002806) baseStart_1002806 baseEnd_1002806 := by
    simpa [prefixWord, tailWord_1002806, baseEnd_1002806] using wordTrace_append hprefix tailTrace_1002806
  have hstable : (prefixWord ++ tailWord_1002806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002806).length < 2 ^ (prefixWord ++ tailWord_1002806).sum := by decide
  have hdescent : baseEnd_1002806 < baseStart_1002806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002815 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 7]
def baseStart_1002815 : Nat := 118140960795 + 1002815 * 2 ^ 59
def prefixEnd_1002815 : Nat := 4983230072969 + 3 ^ 40 * 1002815 * 2
def baseEnd_1002815 : Nat := 114428022786355381200143

theorem tailTrace_1002815 : CollatzResearch.WordTrace tailWord_1002815 prefixEnd_1002815 114428022786355381200143 := by
  unfold tailWord_1002815
  simp only [CollatzResearch.WordTrace]
  refine ⟨36575667861979997011833899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24383778574653331341222599 36575667861979997011833899)
  ·
    refine ⟨54863501792969995517750849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36575667861979997011833899 54863501792969995517750849)
    ·
      refine ⟨41147626344727496638313137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54863501792969995517750849 41147626344727496638313137)
      ·
        refine ⟨30860719758545622478734853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41147626344727496638313137 30860719758545622478734853)
        ·
          refine ⟨5786384954727304214762785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30860719758545622478734853 5786384954727304214762785)
          ·
            refine ⟨4339788716045478161072089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5786384954727304214762785 4339788716045478161072089)
            ·
              refine ⟨3254841537034108620804067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4339788716045478161072089 3254841537034108620804067)
              ·
                refine ⟨4882262305551162931206101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254841537034108620804067 4882262305551162931206101)
                ·
                  refine ⟨114428022786355381200143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4882262305551162931206101 114428022786355381200143)
                  ·
                    rfl

theorem cell22_1002815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 7].length) (baseStart_1002815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002815 prefixEnd_1002815 := by exact prefixLift 1002815
  have htrace : WordTrace (prefixWord ++ tailWord_1002815) baseStart_1002815 baseEnd_1002815 := by
    simpa [prefixWord, tailWord_1002815, baseEnd_1002815] using wordTrace_append hprefix tailTrace_1002815
  have hstable : (prefixWord ++ tailWord_1002815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002815).length < 2 ^ (prefixWord ++ tailWord_1002815).sum := by decide
  have hdescent : baseEnd_1002815 < baseStart_1002815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002830 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1002830 : Nat := 118140960795 + 1002830 * 2 ^ 59
def prefixEnd_1002830 : Nat := 4983230072969 + 3 ^ 40 * 1002830 * 2
def baseEnd_1002830 : Nat := 343289203165611104475383

theorem tailTrace_1002830 : CollatzResearch.WordTrace tailWord_1002830 prefixEnd_1002830 343289203165611104475383 := by
  unfold tailWord_1002830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572026869615706821703743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24384143304617103049086629 4572026869615706821703743)
  ·
    refine ⟨6858040304423560232555615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4572026869615706821703743 6858040304423560232555615)
    ·
      refine ⟨10287060456635340348833423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6858040304423560232555615 10287060456635340348833423)
      ·
        refine ⟨15430590684953010523250135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10287060456635340348833423 15430590684953010523250135)
        ·
          refine ⟨23145886027429515784875203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15430590684953010523250135 23145886027429515784875203)
          ·
            refine ⟨34718829041144273677312805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23145886027429515784875203 34718829041144273677312805)
            ·
              refine ⟨6509780445214551314496151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34718829041144273677312805 6509780445214551314496151)
              ·
                refine ⟨9764670667821826971744227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6509780445214551314496151 9764670667821826971744227)
                ·
                  refine ⟨14647006001732740457616341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764670667821826971744227 14647006001732740457616341)
                  ·
                    refine ⟨343289203165611104475383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14647006001732740457616341 343289203165611104475383)
                    ·
                      rfl

theorem cell22_1002830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1002830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002830 prefixEnd_1002830 := by exact prefixLift 1002830
  have htrace : WordTrace (prefixWord ++ tailWord_1002830) baseStart_1002830 baseEnd_1002830 := by
    simpa [prefixWord, tailWord_1002830, baseEnd_1002830] using wordTrace_append hprefix tailTrace_1002830
  have hstable : (prefixWord ++ tailWord_1002830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002830).length < 2 ^ (prefixWord ++ tailWord_1002830).sum := by decide
  have hdescent : baseEnd_1002830 < baseStart_1002830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002875 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 3, 5]
def baseStart_1002875 : Nat := 118140960795 + 1002875 * 2 ^ 59
def prefixEnd_1002875 : Nat := 4983230072969 + 3 ^ 40 * 1002875 * 2
def baseEnd_1002875 : Nat := 343304607585245987100245

theorem tailTrace_1002875 : CollatzResearch.WordTrace tailWord_1002875 prefixEnd_1002875 343304607585245987100245 := by
  unfold tailWord_1002875
  simp only [CollatzResearch.WordTrace]
  refine ⟨36577856241762627259018079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24385237494508418172678719 36577856241762627259018079)
  ·
    refine ⟨54866784362643940888527119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36577856241762627259018079 54866784362643940888527119)
    ·
      refine ⟨82300176543965911332790679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54866784362643940888527119 82300176543965911332790679)
      ·
        refine ⟨123450264815948866999186019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82300176543965911332790679 123450264815948866999186019)
        ·
          refine ⟨185175397223923300498779029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123450264815948866999186019 185175397223923300498779029)
          ·
            refine ⟨8680096744871404710880267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185175397223923300498779029 8680096744871404710880267)
            ·
              refine ⟨13020145117307107066320401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680096744871404710880267 13020145117307107066320401)
              ·
                refine ⟨9765108837980330299740301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13020145117307107066320401 9765108837980330299740301)
                ·
                  refine ⟨3661915814242623862402613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9765108837980330299740301 3661915814242623862402613)
                  ·
                    refine ⟨343304607585245987100245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3661915814242623862402613 343304607585245987100245)
                    ·
                      rfl

theorem cell22_1002875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_1002875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002875 prefixEnd_1002875 := by exact prefixLift 1002875
  have htrace : WordTrace (prefixWord ++ tailWord_1002875) baseStart_1002875 baseEnd_1002875 := by
    simpa [prefixWord, tailWord_1002875, baseEnd_1002875] using wordTrace_append hprefix tailTrace_1002875
  have hstable : (prefixWord ++ tailWord_1002875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002875).length < 2 ^ (prefixWord ++ tailWord_1002875).sum := by decide
  have hdescent : baseEnd_1002875 < baseStart_1002875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002892 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_1002892 : Nat := 118140960795 + 1002892 * 2 ^ 59
def prefixEnd_1002892 : Nat := 4983230072969 + 3 ^ 40 * 1002892 * 2
def baseEnd_1002892 : Nat := 343310427032663609425193

theorem tailTrace_1002892 : CollatzResearch.WordTrace tailWord_1002892 prefixEnd_1002892 343310427032663609425193 := by
  unfold tailWord_1002892
  simp only [CollatzResearch.WordTrace]
  refine ⟨18289238141350519581193465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24385650855134026108257953 18289238141350519581193465)
  ·
    refine ⟨13716928606012889685895099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18289238141350519581193465 13716928606012889685895099)
    ·
      refine ⟨20575392909019334528842649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13716928606012889685895099 20575392909019334528842649)
      ·
        refine ⟨15431544681764500896631987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20575392909019334528842649 15431544681764500896631987)
        ·
          refine ⟨23147317022646751344947981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15431544681764500896631987 23147317022646751344947981)
          ·
            refine ⟨8680243883492531754355493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23147317022646751344947981 8680243883492531754355493)
            ·
              refine ⟨1627545728154849703941655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8680243883492531754355493 1627545728154849703941655)
              ·
                refine ⟨2441318592232274555912483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627545728154849703941655 2441318592232274555912483)
                ·
                  refine ⟨3661977888348411833868725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441318592232274555912483 3661977888348411833868725)
                  ·
                    refine ⟨343310427032663609425193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3661977888348411833868725 343310427032663609425193)
                    ·
                      rfl

theorem cell22_1002892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_1002892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002892 prefixEnd_1002892 := by exact prefixLift 1002892
  have htrace : WordTrace (prefixWord ++ tailWord_1002892) baseStart_1002892 baseEnd_1002892 := by
    simpa [prefixWord, tailWord_1002892, baseEnd_1002892] using wordTrace_append hprefix tailTrace_1002892
  have hstable : (prefixWord ++ tailWord_1002892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002892).length < 2 ^ (prefixWord ++ tailWord_1002892).sum := by decide
  have hdescent : baseEnd_1002892 < baseStart_1002892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002894 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_1002894 : Nat := 118140960795 + 1002894 * 2 ^ 59
def prefixEnd_1002894 : Nat := 4983230072969 + 3 ^ 40 * 1002894 * 2
def baseEnd_1002894 : Nat := 114437037224512090291729

theorem tailTrace_1002894 : CollatzResearch.WordTrace tailWord_1002894 prefixEnd_1002894 114437037224512090291729 := by
  unfold tailWord_1002894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572318653586724187994967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24385699485795862335973157 4572318653586724187994967)
  ·
    refine ⟨6858477980380086281992451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4572318653586724187994967 6858477980380086281992451)
    ·
      refine ⟨10287716970570129422988677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6858477980380086281992451 10287716970570129422988677)
      ·
        refine ⟨1928946931981899266810377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10287716970570129422988677 1928946931981899266810377)
        ·
          refine ⟨1446710198986424450107783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928946931981899266810377 1446710198986424450107783)
          ·
            refine ⟨2170065298479636675161675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446710198986424450107783 2170065298479636675161675)
            ·
              refine ⟨3255097947719455012742513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170065298479636675161675 3255097947719455012742513)
              ·
                refine ⟨2441323460789591259556885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255097947719455012742513 2441323460789591259556885)
                ·
                  refine ⟨114437037224512090291729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2441323460789591259556885 114437037224512090291729)
                  ·
                    rfl

theorem cell22_1002894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_1002894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002894 prefixEnd_1002894 := by exact prefixLift 1002894
  have htrace : WordTrace (prefixWord ++ tailWord_1002894) baseStart_1002894 baseEnd_1002894 := by
    simpa [prefixWord, tailWord_1002894, baseEnd_1002894] using wordTrace_append hprefix tailTrace_1002894
  have hstable : (prefixWord ++ tailWord_1002894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002894).length < 2 ^ (prefixWord ++ tailWord_1002894).sum := by decide
  have hdescent : baseEnd_1002894 < baseStart_1002894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002954 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_1002954 : Nat := 118140960795 + 1002954 * 2 ^ 59
def prefixEnd_1002954 : Nat := 4983230072969 + 3 ^ 40 * 1002954 * 2
def baseEnd_1002954 : Nat := 343331650899716114375003

theorem tailTrace_1002954 : CollatzResearch.WordTrace tailWord_1002954 prefixEnd_1002954 343331650899716114375003 := by
  unfold tailWord_1002954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145184402119105937785979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24387158405650949167429277 9145184402119105937785979)
  ·
    refine ⟨13717776603178658906678969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9145184402119105937785979 13717776603178658906678969)
    ·
      refine ⟨10288332452383994180009227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13717776603178658906678969 10288332452383994180009227)
      ·
        refine ⟨15432498678575991270013841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10288332452383994180009227 15432498678575991270013841)
        ·
          refine ⟨11574374008931993452510381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15432498678575991270013841 11574374008931993452510381)
          ·
            refine ⟨4340390253349497544691393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11574374008931993452510381 4340390253349497544691393)
            ·
              refine ⟨3255292690012123158518545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340390253349497544691393 3255292690012123158518545)
              ·
                refine ⟨2441469517509092368888909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255292690012123158518545 2441469517509092368888909)
                ·
                  refine ⟨915551069065909638333341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2441469517509092368888909 915551069065909638333341)
                  ·
                    refine ⟨343331650899716114375003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 915551069065909638333341 343331650899716114375003)
                    ·
                      rfl

theorem cell22_1002954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_1002954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1002954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1002954 prefixEnd_1002954 := by exact prefixLift 1002954
  have htrace : WordTrace (prefixWord ++ tailWord_1002954) baseStart_1002954 baseEnd_1002954 := by
    simpa [prefixWord, tailWord_1002954, baseEnd_1002954] using wordTrace_append hprefix tailTrace_1002954
  have hstable : (prefixWord ++ tailWord_1002954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002954).length < 2 ^ (prefixWord ++ tailWord_1002954).sum := by decide
  have hdescent : baseEnd_1002954 < baseStart_1002954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003027 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 3, 5]
def baseStart_1003027 : Nat := 118140960795 + 1003027 * 2 ^ 59
def prefixEnd_1003027 : Nat := 4983230072969 + 3 ^ 40 * 1003027 * 2
def baseEnd_1003027 : Nat := 343356640291568257299779

theorem tailTrace_1003027 : CollatzResearch.WordTrace tailWord_1003027 prefixEnd_1003027 343356640291568257299779 := by
  unfold tailWord_1003027
  simp only [CollatzResearch.WordTrace]
  refine ⟨36583400137211957218551335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24388933424807971479034223 36583400137211957218551335)
  ·
    refine ⟨54875100205817935827827003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36583400137211957218551335 54875100205817935827827003)
    ·
      refine ⟨82312650308726903741740505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54875100205817935827827003 82312650308726903741740505)
      ·
        refine ⟨61734487731545177806305379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82312650308726903741740505 61734487731545177806305379)
        ·
          refine ⟨92601731597317766709458069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61734487731545177806305379 92601731597317766709458069)
          ·
            refine ⟨4340706168624270314505847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92601731597317766709458069 4340706168624270314505847)
            ·
              refine ⟨6511059252936405471758771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340706168624270314505847 6511059252936405471758771)
              ·
                refine ⟨9766588879404608207638157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511059252936405471758771 9766588879404608207638157)
                ·
                  refine ⟨3662470829776728077864309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9766588879404608207638157 3662470829776728077864309)
                  ·
                    refine ⟨343356640291568257299779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3662470829776728077864309 343356640291568257299779)
                    ·
                      rfl

theorem cell22_1003027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_1003027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003027 prefixEnd_1003027 := by exact prefixLift 1003027
  have htrace : WordTrace (prefixWord ++ tailWord_1003027) baseStart_1003027 baseEnd_1003027 := by
    simpa [prefixWord, tailWord_1003027, baseEnd_1003027] using wordTrace_append hprefix tailTrace_1003027
  have hstable : (prefixWord ++ tailWord_1003027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003027).length < 2 ^ (prefixWord ++ tailWord_1003027).sum := by decide
  have hdescent : baseEnd_1003027 < baseStart_1003027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003061 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1003061 : Nat := 118140960795 + 1003061 * 2 ^ 59
def prefixEnd_1003061 : Nat := 4983230072969 + 3 ^ 40 * 1003061 * 2
def baseEnd_1003061 : Nat := 343368279186403501949675

theorem tailTrace_1003061 : CollatzResearch.WordTrace tailWord_1003061 prefixEnd_1003061 343368279186403501949675 := by
  unfold tailWord_1003061
  simp only [CollatzResearch.WordTrace]
  refine ⟨36584640219088781025289037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24389760146059187350192691 36584640219088781025289037)
  ·
    refine ⟨13719240082158292884483389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36584640219088781025289037 13719240082158292884483389)
    ·
      refine ⟨5144715030809359831681271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13719240082158292884483389 5144715030809359831681271)
      ·
        refine ⟨7717072546214039747521907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144715030809359831681271 7717072546214039747521907)
        ·
          refine ⟨11575608819321059621282861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717072546214039747521907 11575608819321059621282861)
          ·
            refine ⟨4340853307245397357981073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11575608819321059621282861 4340853307245397357981073)
            ·
              refine ⟨3255639980434048018485805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340853307245397357981073 3255639980434048018485805)
              ·
                refine ⟨1220864992662768006932177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3255639980434048018485805 1220864992662768006932177)
                ·
                  refine ⟨915648744497076005199133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1220864992662768006932177 915648744497076005199133)
                  ·
                    refine ⟨343368279186403501949675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 915648744497076005199133 343368279186403501949675)
                    ·
                      rfl

theorem cell22_1003061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1003061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003061 prefixEnd_1003061 := by exact prefixLift 1003061
  have htrace : WordTrace (prefixWord ++ tailWord_1003061) baseStart_1003061 baseEnd_1003061 := by
    simpa [prefixWord, tailWord_1003061, baseEnd_1003061] using wordTrace_append hprefix tailTrace_1003061
  have hstable : (prefixWord ++ tailWord_1003061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003061).length < 2 ^ (prefixWord ++ tailWord_1003061).sum := by decide
  have hdescent : baseEnd_1003061 < baseStart_1003061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003089 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 5, 3]
def baseStart_1003089 : Nat := 118140960795 + 1003089 * 2 ^ 59
def prefixEnd_1003089 : Nat := 4983230072969 + 3 ^ 40 * 1003089 * 2
def baseEnd_1003089 : Nat := 343377864158620762249589

theorem tailTrace_1003089 : CollatzResearch.WordTrace tailWord_1003089 prefixEnd_1003089 343377864158620762249589 := by
  unfold tailWord_1003089
  simp only [CollatzResearch.WordTrace]
  refine ⟨36585661462987341807308321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24390440975324894538205547 36585661462987341807308321)
  ·
    refine ⟨27439246097240506355481241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36585661462987341807308321 27439246097240506355481241)
    ·
      refine ⟨20579434572930379766610931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27439246097240506355481241 20579434572930379766610931)
      ·
        refine ⟨30869151859395569649916397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20579434572930379766610931 30869151859395569649916397)
        ·
          refine ⟨11575931947273338618718649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30869151859395569649916397 11575931947273338618718649)
          ·
            refine ⟨8681948960455003964038987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11575931947273338618718649 8681948960455003964038987)
            ·
              refine ⟨13022923440682505946058481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681948960455003964038987 13022923440682505946058481)
              ·
                refine ⟨9767192580511879459543861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13022923440682505946058481 9767192580511879459543861)
                ·
                  refine ⟨915674304422988699332237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9767192580511879459543861 915674304422988699332237)
                  ·
                    refine ⟨343377864158620762249589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 915674304422988699332237 343377864158620762249589)
                    ·
                      rfl

theorem cell22_1003089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_1003089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003089 prefixEnd_1003089 := by exact prefixLift 1003089
  have htrace : WordTrace (prefixWord ++ tailWord_1003089) baseStart_1003089 baseEnd_1003089 := by
    simpa [prefixWord, tailWord_1003089, baseEnd_1003089] using wordTrace_append hprefix tailTrace_1003089
  have hstable : (prefixWord ++ tailWord_1003089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003089).length < 2 ^ (prefixWord ++ tailWord_1003089).sum := by decide
  have hdescent : baseEnd_1003089 < baseStart_1003089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003196 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_1003196 : Nat := 118140960795 + 1003196 * 2 ^ 59
def prefixEnd_1003196 : Nat := 4983230072969 + 3 ^ 40 * 1003196 * 2
def baseEnd_1003196 : Nat := 343414492445308149824261

theorem tailTrace_1003196 : CollatzResearch.WordTrace tailWord_1003196 prefixEnd_1003196 343414492445308149824261 := by
  unfold tailWord_1003196
  simp only [CollatzResearch.WordTrace]
  refine ⟨18294782036799849540726721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24393042715733132720968961 18294782036799849540726721)
  ·
    refine ⟨13721086527599887155545041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18294782036799849540726721 13721086527599887155545041)
    ·
      refine ⟨10290814895699915366658781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13721086527599887155545041 10290814895699915366658781)
      ·
        refine ⟨3859055585887468262497043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10290814895699915366658781 3859055585887468262497043)
        ·
          refine ⟨5788583378831202393745565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859055585887468262497043 5788583378831202393745565)
          ·
            refine ⟨2170718767061700897654587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5788583378831202393745565 2170718767061700897654587)
            ·
              refine ⟨3256078150592551346481881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170718767061700897654587 3256078150592551346481881)
              ·
                refine ⟨2442058612944413509861411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3256078150592551346481881 2442058612944413509861411)
                ·
                  refine ⟨3663087919416620264792117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442058612944413509861411 3663087919416620264792117)
                  ·
                    refine ⟨343414492445308149824261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3663087919416620264792117 343414492445308149824261)
                    ·
                      rfl

theorem cell22_1003196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_1003196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003196 prefixEnd_1003196 := by exact prefixLift 1003196
  have htrace : WordTrace (prefixWord ++ tailWord_1003196) baseStart_1003196 baseEnd_1003196 := by
    simpa [prefixWord, tailWord_1003196, baseEnd_1003196] using wordTrace_append hprefix tailTrace_1003196
  have hstable : (prefixWord ++ tailWord_1003196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003196).length < 2 ^ (prefixWord ++ tailWord_1003196).sum := by decide
  have hdescent : baseEnd_1003196 < baseStart_1003196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003226 : List Nat := [3, 1, 1, 2, 2, 5, 1, 7]
def baseStart_1003226 : Nat := 118140960795 + 1003226 * 2 ^ 59
def prefixEnd_1003226 : Nat := 4983230072969 + 3 ^ 40 * 1003226 * 2
def baseEnd_1003226 : Nat := 38158306895377563508241

theorem tailTrace_1003226 : CollatzResearch.WordTrace tailWord_1003226 prefixEnd_1003226 38158306895377563508241 := by
  unfold tailWord_1003226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9147664565872753551261383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24393772175660676136697021 9147664565872753551261383)
  ·
    refine ⟨13721496848809130326892075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9147664565872753551261383 13721496848809130326892075)
    ·
      refine ⟨20582245273213695490338113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13721496848809130326892075 20582245273213695490338113)
      ·
        refine ⟨15436683954910271617753585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20582245273213695490338113 15436683954910271617753585)
        ·
          refine ⟨11577512966182703713315189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15436683954910271617753585 11577512966182703713315189)
          ·
            refine ⟨1085391840579628473123299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11577512966182703713315189 1085391840579628473123299)
            ·
              refine ⟨1628087760869442709684949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085391840579628473123299 1628087760869442709684949)
              ·
                refine ⟨38158306895377563508241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1628087760869442709684949 38158306895377563508241)
                ·
                  rfl

theorem cell22_1003226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_1003226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003226 prefixEnd_1003226 := by exact prefixLift 1003226
  have htrace : WordTrace (prefixWord ++ tailWord_1003226) baseStart_1003226 baseEnd_1003226 := by
    simpa [prefixWord, tailWord_1003226, baseEnd_1003226] using wordTrace_append hprefix tailTrace_1003226
  have hstable : (prefixWord ++ tailWord_1003226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003226).length < 2 ^ (prefixWord ++ tailWord_1003226).sum := by decide
  have hdescent : baseEnd_1003226 < baseStart_1003226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003294 : List Nat := [4, 3, 2, 2, 2, 1, 2, 6]
def baseStart_1003294 : Nat := 118140960795 + 1003294 * 2 ^ 59
def prefixEnd_1003294 : Nat := 4983230072969 + 3 ^ 40 * 1003294 * 2
def baseEnd_1003294 : Nat := 38160893316452062319329

theorem tailTrace_1003294 : CollatzResearch.WordTrace tailWord_1003294 prefixEnd_1003294 38160893316452062319329 := by
  unfold tailWord_1003294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574142303405582727315117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24395425618163107879013957 4574142303405582727315117)
  ·
    refine ⟨1715303363777093522743169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4574142303405582727315117 1715303363777093522743169)
    ·
      refine ⟨1286477522832820142057377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1715303363777093522743169 1286477522832820142057377)
      ·
        refine ⟨964858142124615106543033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1286477522832820142057377 964858142124615106543033)
        ·
          refine ⟨723643606593461329907275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964858142124615106543033 723643606593461329907275)
          ·
            refine ⟨1085465409890191994860913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723643606593461329907275 1085465409890191994860913)
            ·
              refine ⟨814099057417643996145685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085465409890191994860913 814099057417643996145685)
              ·
                refine ⟨38160893316452062319329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 814099057417643996145685 38160893316452062319329)
                ·
                  rfl

theorem cell22_1003294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_1003294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003294 prefixEnd_1003294 := by exact prefixLift 1003294
  have htrace : WordTrace (prefixWord ++ tailWord_1003294) baseStart_1003294 baseEnd_1003294 := by
    simpa [prefixWord, tailWord_1003294, baseEnd_1003294] using wordTrace_append hprefix tailTrace_1003294
  have hstable : (prefixWord ++ tailWord_1003294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003294).length < 2 ^ (prefixWord ++ tailWord_1003294).sum := by decide
  have hdescent : baseEnd_1003294 < baseStart_1003294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003410 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1003410 : Nat := 118140960795 + 1003410 * 2 ^ 59
def prefixEnd_1003410 : Nat := 4983230072969 + 3 ^ 40 * 1003410 * 2
def baseEnd_1003410 : Nat := 343487749018682924973605

theorem tailTrace_1003410 : CollatzResearch.WordTrace tailWord_1003410 prefixEnd_1003410 343487749018682924973605 := by
  unfold tailWord_1003410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149342323706103407435921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24398246196549609086495789 9149342323706103407435921)
  ·
    refine ⟨6862006742779577555576941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9149342323706103407435921 6862006742779577555576941)
    ·
      refine ⟨2573252528542341583341353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6862006742779577555576941 2573252528542341583341353)
      ·
        refine ⟨1929939396406756187506015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2573252528542341583341353 1929939396406756187506015)
        ·
          refine ⟨2894909094610134281259023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929939396406756187506015 2894909094610134281259023)
          ·
            refine ⟨4342363641915201421888535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894909094610134281259023 4342363641915201421888535)
            ·
              refine ⟨6513545462872802132832803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342363641915201421888535 6513545462872802132832803)
              ·
                refine ⟨9770318194309203199249205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513545462872802132832803 9770318194309203199249205)
                ·
                  refine ⟨915967330716487799929613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9770318194309203199249205 915967330716487799929613)
                  ·
                    refine ⟨343487749018682924973605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 915967330716487799929613 343487749018682924973605)
                    ·
                      rfl

theorem cell22_1003410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1003410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003410 prefixEnd_1003410 := by exact prefixLift 1003410
  have htrace : WordTrace (prefixWord ++ tailWord_1003410) baseStart_1003410 baseEnd_1003410 := by
    simpa [prefixWord, tailWord_1003410, baseEnd_1003410] using wordTrace_append hprefix tailTrace_1003410
  have hstable : (prefixWord ++ tailWord_1003410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003410).length < 2 ^ (prefixWord ++ tailWord_1003410).sum := by decide
  have hdescent : baseEnd_1003410 < baseStart_1003410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003444 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1003444 : Nat := 118140960795 + 1003444 * 2 ^ 59
def prefixEnd_1003444 : Nat := 4983230072969 + 3 ^ 40 * 1003444 * 2
def baseEnd_1003444 : Nat := 343499387913518169623501

theorem tailTrace_1003444 : CollatzResearch.WordTrace tailWord_1003444 prefixEnd_1003444 343499387913518169623501 := by
  unfold tailWord_1003444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299304688350618718240693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24399072917800824957654257 18299304688350618718240693)
  ·
    refine ⟨1715559814532870504835065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18299304688350618718240693 1715559814532870504835065)
    ·
      refine ⟨1286669860899652878626299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1715559814532870504835065 1286669860899652878626299)
      ·
        refine ⟨1930004791349479317939449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286669860899652878626299 1930004791349479317939449)
        ·
          refine ⟨1447503593512109488454587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930004791349479317939449 1447503593512109488454587)
          ·
            refine ⟨2171255390268164232681881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447503593512109488454587 2171255390268164232681881)
            ·
              refine ⟨1628441542701123174511411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171255390268164232681881 1628441542701123174511411)
              ·
                refine ⟨2442662314051684761767117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628441542701123174511411 2442662314051684761767117)
                ·
                  refine ⟨915998367769381785662669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2442662314051684761767117 915998367769381785662669)
                  ·
                    refine ⟨343499387913518169623501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 915998367769381785662669 343499387913518169623501)
                    ·
                      rfl

theorem cell22_1003444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1003444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003444 prefixEnd_1003444 := by exact prefixLift 1003444
  have htrace : WordTrace (prefixWord ++ tailWord_1003444) baseStart_1003444 baseEnd_1003444 := by
    simpa [prefixWord, tailWord_1003444, baseEnd_1003444] using wordTrace_append hprefix tailTrace_1003444
  have hstable : (prefixWord ++ tailWord_1003444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003444).length < 2 ^ (prefixWord ++ tailWord_1003444).sum := by decide
  have hdescent : baseEnd_1003444 < baseStart_1003444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003451 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 6]
def baseStart_1003451 : Nat := 118140960795 + 1003451 * 2 ^ 59
def prefixEnd_1003451 : Nat := 4983230072969 + 3 ^ 40 * 1003451 * 2
def baseEnd_1003451 : Nat := 114500594718857494899493

theorem tailTrace_1003451 : CollatzResearch.WordTrace tailWord_1003451 prefixEnd_1003451 114500594718857494899493 := by
  unfold tailWord_1003451
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598864687675877631986207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24399243125117251754657471 36598864687675877631986207)
  ·
    refine ⟨54898297031513816447979311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36598864687675877631986207 54898297031513816447979311)
    ·
      refine ⟨82347445547270724671968967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54898297031513816447979311 82347445547270724671968967)
      ·
        refine ⟨123521168320906087007953451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82347445547270724671968967 123521168320906087007953451)
        ·
          refine ⟨185281752481359130511930177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123521168320906087007953451 185281752481359130511930177)
          ·
            refine ⟨138961314361019347883947633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185281752481359130511930177 138961314361019347883947633)
            ·
              refine ⟨104220985770764510912960725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138961314361019347883947633 104220985770764510912960725)
              ·
                refine ⟨2442679354002293224522517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104220985770764510912960725 2442679354002293224522517)
                ·
                  refine ⟨114500594718857494899493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2442679354002293224522517 114500594718857494899493)
                  ·
                    rfl

theorem cell22_1003451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 6].length) (baseStart_1003451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003451 prefixEnd_1003451 := by exact prefixLift 1003451
  have htrace : WordTrace (prefixWord ++ tailWord_1003451) baseStart_1003451 baseEnd_1003451 := by
    simpa [prefixWord, tailWord_1003451, baseEnd_1003451] using wordTrace_append hprefix tailTrace_1003451
  have hstable : (prefixWord ++ tailWord_1003451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003451).length < 2 ^ (prefixWord ++ tailWord_1003451).sum := by decide
  have hdescent : baseEnd_1003451 < baseStart_1003451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003468 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 6]
def baseStart_1003468 : Nat := 118140960795 + 1003468 * 2 ^ 59
def prefixEnd_1003468 : Nat := 4983230072969 + 3 ^ 40 * 1003468 * 2
def baseEnd_1003468 : Nat := 114502534534663369007809

theorem tailTrace_1003468 : CollatzResearch.WordTrace tailWord_1003468 prefixEnd_1003468 114502534534663369007809 := by
  unfold tailWord_1003468
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299742364307144767677529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24399656485742859690236705 18299742364307144767677529)
  ·
    refine ⟨13724806773230358575758147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18299742364307144767677529 13724806773230358575758147)
    ·
      refine ⟨20587210159845537863637221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13724806773230358575758147 20587210159845537863637221)
      ·
        refine ⟨3860101904971038349431979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20587210159845537863637221 3860101904971038349431979)
        ·
          refine ⟨5790152857456557524147969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860101904971038349431979 5790152857456557524147969)
          ·
            refine ⟨4342614643092418143110977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5790152857456557524147969 4342614643092418143110977)
            ·
              refine ⟨3256960982319313607333233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4342614643092418143110977 3256960982319313607333233)
              ·
                refine ⟨2442720736739485205499925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3256960982319313607333233 2442720736739485205499925)
                ·
                  refine ⟨114502534534663369007809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2442720736739485205499925 114502534534663369007809)
                  ·
                    rfl

theorem cell22_1003468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_1003468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003468 prefixEnd_1003468 := by exact prefixLift 1003468
  have htrace : WordTrace (prefixWord ++ tailWord_1003468) baseStart_1003468 baseEnd_1003468 := by
    simpa [prefixWord, tailWord_1003468, baseEnd_1003468] using wordTrace_append hprefix tailTrace_1003468
  have hstable : (prefixWord ++ tailWord_1003468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003468).length < 2 ^ (prefixWord ++ tailWord_1003468).sum := by decide
  have hdescent : baseEnd_1003468 < baseStart_1003468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003470 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_1003470 : Nat := 118140960795 + 1003470 * 2 ^ 59
def prefixEnd_1003470 : Nat := 4983230072969 + 3 ^ 40 * 1003470 * 2
def baseEnd_1003470 : Nat := 343508288244862768473421

theorem tailTrace_1003470 : CollatzResearch.WordTrace tailWord_1003470 prefixEnd_1003470 343508288244862768473421 := by
  unfold tailWord_1003470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574944709325880484615983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24399705116404695917951909 4574944709325880484615983)
  ·
    refine ⟨6862417063988820726923975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4574944709325880484615983 6862417063988820726923975)
    ·
      refine ⟨10293625595983231090385963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6862417063988820726923975 10293625595983231090385963)
      ·
        refine ⟨15440438393974846635578945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10293625595983231090385963 15440438393974846635578945)
        ·
          refine ⟨11580328795481134976684209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15440438393974846635578945 11580328795481134976684209)
          ·
            refine ⟨8685246596610851232513157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11580328795481134976684209 8685246596610851232513157)
            ·
              refine ⟨1628483736864534606096217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8685246596610851232513157 1628483736864534606096217)
              ·
                refine ⟨1221362802648400954572163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1628483736864534606096217 1221362802648400954572163)
                ·
                  refine ⟨1832044203972601431858245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221362802648400954572163 1832044203972601431858245)
                  ·
                    refine ⟨343508288244862768473421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1832044203972601431858245 343508288244862768473421)
                    ·
                      rfl

theorem cell22_1003470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_1003470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003470 prefixEnd_1003470 := by exact prefixLift 1003470
  have htrace : WordTrace (prefixWord ++ tailWord_1003470) baseStart_1003470 baseEnd_1003470 := by
    simpa [prefixWord, tailWord_1003470, baseEnd_1003470] using wordTrace_append hprefix tailTrace_1003470
  have hstable : (prefixWord ++ tailWord_1003470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003470).length < 2 ^ (prefixWord ++ tailWord_1003470).sum := by decide
  have hdescent : baseEnd_1003470 < baseStart_1003470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003478 : List Nat := [5, 2, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1003478 : Nat := 118140960795 + 1003478 * 2 ^ 59
def prefixEnd_1003478 : Nat := 4983230072969 + 3 ^ 40 * 1003478 * 2
def baseEnd_1003478 : Nat := 343511026808353414273397

theorem tailTrace_1003478 : CollatzResearch.WordTrace tailWord_1003478 prefixEnd_1003478 343511026808353414273397 := by
  unfold tailWord_1003478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287490591161128827701193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24399899639052040828812725 2287490591161128827701193)
  ·
    refine ⟨1715617943370846620775895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2287490591161128827701193 1715617943370846620775895)
    ·
      refine ⟨2573426915056269931163843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1715617943370846620775895 2573426915056269931163843)
      ·
        refine ⟨3860140372584404896745765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573426915056269931163843 3860140372584404896745765)
        ·
          refine ⟨723776319859575918139831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3860140372584404896745765 723776319859575918139831)
          ·
            refine ⟨1085664479789363877209747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723776319859575918139831 1085664479789363877209747)
            ·
              refine ⟨1628496719684045815814621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085664479789363877209747 1628496719684045815814621)
              ·
                refine ⟨610686269881517180930483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1628496719684045815814621 610686269881517180930483)
                ·
                  refine ⟨916029404822275771395725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610686269881517180930483 916029404822275771395725)
                  ·
                    refine ⟨343511026808353414273397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 916029404822275771395725 343511026808353414273397)
                    ·
                      rfl

theorem cell22_1003478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1003478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003478 prefixEnd_1003478 := by exact prefixLift 1003478
  have htrace : WordTrace (prefixWord ++ tailWord_1003478) baseStart_1003478 baseEnd_1003478 := by
    simpa [prefixWord, tailWord_1003478, baseEnd_1003478] using wordTrace_append hprefix tailTrace_1003478
  have hstable : (prefixWord ++ tailWord_1003478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003478).length < 2 ^ (prefixWord ++ tailWord_1003478).sum := by decide
  have hdescent : baseEnd_1003478 < baseStart_1003478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003513 : List Nat := [1, 2, 1, 3, 1, 5, 2, 7]
def baseStart_1003513 : Nat := 118140960795 + 1003513 * 2 ^ 59
def prefixEnd_1003513 : Nat := 4983230072969 + 3 ^ 40 * 1003513 * 2
def baseEnd_1003513 : Nat := 38169223113736109960921

theorem tailTrace_1003513 : CollatzResearch.WordTrace tailWord_1003513 prefixEnd_1003513 38169223113736109960921 := by
  unfold tailWord_1003513
  simp only [CollatzResearch.WordTrace]
  refine ⟨36601126013451262220743193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24400750675634174813828795 36601126013451262220743193)
  ·
    refine ⟨27450844510088446665557395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36601126013451262220743193 27450844510088446665557395)
    ·
      refine ⟨41176266765132669998336093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27450844510088446665557395 41176266765132669998336093)
      ·
        refine ⟨15441100036924751249376035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41176266765132669998336093 15441100036924751249376035)
        ·
          refine ⟨23161650055387126874064053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15441100036924751249376035 23161650055387126874064053)
          ·
            refine ⟨2171404692692543144443505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23161650055387126874064053 2171404692692543144443505)
            ·
              refine ⟨1628553519519407358332629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171404692692543144443505 1628553519519407358332629)
              ·
                refine ⟨38169223113736109960921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1628553519519407358332629 38169223113736109960921)
                ·
                  rfl

theorem cell22_1003513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 7].length) (baseStart_1003513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003513 prefixEnd_1003513 := by exact prefixLift 1003513
  have htrace : WordTrace (prefixWord ++ tailWord_1003513) baseStart_1003513 baseEnd_1003513 := by
    simpa [prefixWord, tailWord_1003513, baseEnd_1003513] using wordTrace_append hprefix tailTrace_1003513
  have hstable : (prefixWord ++ tailWord_1003513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003513).length < 2 ^ (prefixWord ++ tailWord_1003513).sum := by decide
  have hdescent : baseEnd_1003513 < baseStart_1003513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003517 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_1003517 : Nat := 118140960795 + 1003517 * 2 ^ 59
def prefixEnd_1003517 : Nat := 4983230072969 + 3 ^ 40 * 1003517 * 2
def baseEnd_1003517 : Nat := 343524377305370312548277

theorem tailTrace_1003517 : CollatzResearch.WordTrace tailWord_1003517 prefixEnd_1003517 343524377305370312548277 := by
  unfold tailWord_1003517
  simp only [CollatzResearch.WordTrace]
  refine ⟨36601271905436770903888805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24400847936957847269259203 36601271905436770903888805)
  ·
    refine ⟨6862738482269394544479151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36601271905436770903888805 6862738482269394544479151)
    ·
      refine ⟨10294107723404091816718727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6862738482269394544479151 10294107723404091816718727)
      ·
        refine ⟨15441161585106137725078091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10294107723404091816718727 15441161585106137725078091)
        ·
          refine ⟨23161742377659206587617137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15441161585106137725078091 23161742377659206587617137)
          ·
            refine ⟨17371306783244404940712853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23161742377659206587617137 17371306783244404940712853)
            ·
              refine ⟨814280005464581481595915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17371306783244404940712853 814280005464581481595915)
              ·
                refine ⟨1221420008196872222393873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814280005464581481595915 1221420008196872222393873)
                ·
                  refine ⟨916065006147654166795405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1221420008196872222393873 916065006147654166795405)
                  ·
                    refine ⟨343524377305370312548277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 916065006147654166795405 343524377305370312548277)
                    ·
                      rfl

theorem cell22_1003517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_1003517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003517 prefixEnd_1003517 := by exact prefixLift 1003517
  have htrace : WordTrace (prefixWord ++ tailWord_1003517) baseStart_1003517 baseEnd_1003517 := by
    simpa [prefixWord, tailWord_1003517, baseEnd_1003517] using wordTrace_append hprefix tailTrace_1003517
  have hstable : (prefixWord ++ tailWord_1003517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003517).length < 2 ^ (prefixWord ++ tailWord_1003517).sum := by decide
  have hdescent : baseEnd_1003517 < baseStart_1003517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003573 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1003573 : Nat := 118140960795 + 1003573 * 2 ^ 59
def prefixEnd_1003573 : Nat := 4983230072969 + 3 ^ 40 * 1003573 * 2
def baseEnd_1003573 : Nat := 343543547249804833148105

theorem tailTrace_1003573 : CollatzResearch.WordTrace tailWord_1003573 prefixEnd_1003573 343543547249804833148105 := by
  unfold tailWord_1003573
  simp only [CollatzResearch.WordTrace]
  refine ⟨36603314393233892467927373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24402209595489261645284915 36603314393233892467927373)
  ·
    refine ⟨13726242897462709675472765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36603314393233892467927373 13726242897462709675472765)
    ·
      refine ⟨5147341086548516128302287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13726242897462709675472765 5147341086548516128302287)
      ·
        refine ⟨7721011629822774192453431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147341086548516128302287 7721011629822774192453431)
        ·
          refine ⟨11581517444734161288680147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7721011629822774192453431 11581517444734161288680147)
          ·
            refine ⟨17372276167101241933020221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11581517444734161288680147 17372276167101241933020221)
            ·
              refine ⟨6514603562662965724882583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17372276167101241933020221 6514603562662965724882583)
              ·
                refine ⟨9771905343994448587323875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6514603562662965724882583 9771905343994448587323875)
                ·
                  refine ⟨14657858015991672880985813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9771905343994448587323875 14657858015991672880985813)
                  ·
                    refine ⟨343543547249804833148105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14657858015991672880985813 343543547249804833148105)
                    ·
                      rfl

theorem cell22_1003573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1003573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003573 prefixEnd_1003573 := by exact prefixLift 1003573
  have htrace : WordTrace (prefixWord ++ tailWord_1003573) baseStart_1003573 baseEnd_1003573 := by
    simpa [prefixWord, tailWord_1003573, baseEnd_1003573] using wordTrace_append hprefix tailTrace_1003573
  have hstable : (prefixWord ++ tailWord_1003573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003573).length < 2 ^ (prefixWord ++ tailWord_1003573).sum := by decide
  have hdescent : baseEnd_1003573 < baseStart_1003573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003633 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_1003633 : Nat := 118140960795 + 1003633 * 2 ^ 59
def prefixEnd_1003633 : Nat := 4983230072969 + 3 ^ 40 * 1003633 * 2
def baseEnd_1003633 : Nat := 343564086475984676647921

theorem tailTrace_1003633 : CollatzResearch.WordTrace tailWord_1003633 prefixEnd_1003633 343564086475984676647921 := by
  unfold tailWord_1003633
  simp only [CollatzResearch.WordTrace]
  refine ⟨36605502773016522715111553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24403668515344348476741035 36605502773016522715111553)
  ·
    refine ⟨27454127079762392036333665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36605502773016522715111553 27454127079762392036333665)
    ·
      refine ⟨20590595309821794027250249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27454127079762392036333665 20590595309821794027250249)
      ·
        refine ⟨15442946482366345520437687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20590595309821794027250249 15442946482366345520437687)
        ·
          refine ⟨23164419723549518280656531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15442946482366345520437687 23164419723549518280656531)
          ·
            refine ⟨34746629585324277420984797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23164419723549518280656531 34746629585324277420984797)
            ·
              refine ⟨13029986094496604032869299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34746629585324277420984797 13029986094496604032869299)
              ·
                refine ⟨19544979141744906049303949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13029986094496604032869299 19544979141744906049303949)
                ·
                  refine ⟨7329367178154339768488981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19544979141744906049303949 7329367178154339768488981)
                  ·
                    refine ⟨343564086475984676647921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7329367178154339768488981 343564086475984676647921)
                    ·
                      rfl

theorem cell22_1003633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_1003633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003633 prefixEnd_1003633 := by exact prefixLift 1003633
  have htrace : WordTrace (prefixWord ++ tailWord_1003633) baseStart_1003633 baseEnd_1003633 := by
    simpa [prefixWord, tailWord_1003633, baseEnd_1003633] using wordTrace_append hprefix tailTrace_1003633
  have hstable : (prefixWord ++ tailWord_1003633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003633).length < 2 ^ (prefixWord ++ tailWord_1003633).sum := by decide
  have hdescent : baseEnd_1003633 < baseStart_1003633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003682 : List Nat := [3, 3, 1, 3, 1, 2, 2, 7]
def baseStart_1003682 : Nat := 118140960795 + 1003682 * 2 ^ 59
def prefixEnd_1003682 : Nat := 4983230072969 + 3 ^ 40 * 1003682 * 2
def baseEnd_1003682 : Nat := 38175651130818320241419

theorem tailTrace_1003682 : CollatzResearch.WordTrace tailWord_1003682 prefixEnd_1003682 38175651130818320241419 := by
  unfold tailWord_1003682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151822487459751020911325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24404859966559336055763533 9151822487459751020911325)
  ·
    refine ⟨3431933432797406632841747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9151822487459751020911325 3431933432797406632841747)
    ·
      refine ⟨5147900149196109949262621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3431933432797406632841747 5147900149196109949262621)
      ·
        refine ⟨1930462555948541230973483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5147900149196109949262621 1930462555948541230973483)
        ·
          refine ⟨2895693833922811846460225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930462555948541230973483 2895693833922811846460225)
          ·
            refine ⟨2171770375442108884845169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2895693833922811846460225 2171770375442108884845169)
            ·
              refine ⟨1628827781581581663633877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171770375442108884845169 1628827781581581663633877)
              ·
                refine ⟨38175651130818320241419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1628827781581581663633877 38175651130818320241419)
                ·
                  rfl

theorem cell22_1003682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_1003682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003682 prefixEnd_1003682 := by exact prefixLift 1003682
  have htrace : WordTrace (prefixWord ++ tailWord_1003682) baseStart_1003682 baseEnd_1003682 := by
    simpa [prefixWord, tailWord_1003682, baseEnd_1003682] using wordTrace_append hprefix tailTrace_1003682
  have hstable : (prefixWord ++ tailWord_1003682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003682).length < 2 ^ (prefixWord ++ tailWord_1003682).sum := by decide
  have hdescent : baseEnd_1003682 < baseStart_1003682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003755 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 6]
def baseStart_1003755 : Nat := 118140960795 + 1003755 * 2 ^ 59
def prefixEnd_1003755 : Nat := 4983230072969 + 3 ^ 40 * 1003755 * 2
def baseEnd_1003755 : Nat := 114535283189739008365849

theorem tailTrace_1003755 : CollatzResearch.WordTrace tailWord_1003755 prefixEnd_1003755 114535283189739008365849 := by
  unfold tailWord_1003755
  simp only [CollatzResearch.WordTrace]
  refine ⟨36609952478574537551052719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24406634985716358367368479 36609952478574537551052719)
  ·
    refine ⟨54914928717861806326579079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36609952478574537551052719 54914928717861806326579079)
    ·
      refine ⟨82372393076792709489868619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54914928717861806326579079 82372393076792709489868619)
      ·
        refine ⟨123558589615189064234802929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82372393076792709489868619 123558589615189064234802929)
        ·
          refine ⟨92668942211391798176102197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123558589615189064234802929 92668942211391798176102197)
          ·
            refine ⟨8687713332317981079009581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92668942211391798176102197 8687713332317981079009581)
            ·
              refine ⟨3257892499619242904628593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8687713332317981079009581 3257892499619242904628593)
              ·
                refine ⟨2443419374714432178471445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3257892499619242904628593 2443419374714432178471445)
                ·
                  refine ⟨114535283189739008365849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2443419374714432178471445 114535283189739008365849)
                  ·
                    rfl

theorem cell22_1003755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 6].length) (baseStart_1003755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003755 prefixEnd_1003755 := by exact prefixLift 1003755
  have htrace : WordTrace (prefixWord ++ tailWord_1003755) baseStart_1003755 baseEnd_1003755 := by
    simpa [prefixWord, tailWord_1003755, baseEnd_1003755] using wordTrace_append hprefix tailTrace_1003755
  have hstable : (prefixWord ++ tailWord_1003755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003755).length < 2 ^ (prefixWord ++ tailWord_1003755).sum := by decide
  have hdescent : baseEnd_1003755 < baseStart_1003755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003774 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1003774 : Nat := 118140960795 + 1003774 * 2 ^ 59
def prefixEnd_1003774 : Nat := 4983230072969 + 3 ^ 40 * 1003774 * 2
def baseEnd_1003774 : Nat := 343612353657507308872489

theorem tailTrace_1003774 : CollatzResearch.WordTrace tailWord_1003774 prefixEnd_1003774 343612353657507308872489 := by
  unfold tailWord_1003774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576330683188212974499297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24407096977003802530662917 4576330683188212974499297)
  ·
    refine ⟨3432248012391159730874473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4576330683188212974499297 3432248012391159730874473)
    ·
      refine ⟨2574186009293369798155855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3432248012391159730874473 2574186009293369798155855)
      ·
        refine ⟨3861279013940054697233783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574186009293369798155855 3861279013940054697233783)
        ·
          refine ⟨5791918520910082045850675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861279013940054697233783 5791918520910082045850675)
          ·
            refine ⟨8687877781365123068776013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791918520910082045850675 8687877781365123068776013)
            ·
              refine ⟨3257954168011921150791005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8687877781365123068776013 3257954168011921150791005)
              ·
                refine ⟨1221732813004470431546627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3257954168011921150791005 1221732813004470431546627)
                ·
                  refine ⟨1832599219506705647319941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221732813004470431546627 1832599219506705647319941)
                  ·
                    refine ⟨343612353657507308872489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1832599219506705647319941 343612353657507308872489)
                    ·
                      rfl

theorem cell22_1003774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1003774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003774 prefixEnd_1003774 := by exact prefixLift 1003774
  have htrace : WordTrace (prefixWord ++ tailWord_1003774) baseStart_1003774 baseEnd_1003774 := by
    simpa [prefixWord, tailWord_1003774, baseEnd_1003774] using wordTrace_append hprefix tailTrace_1003774
  have hstable : (prefixWord ++ tailWord_1003774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003774).length < 2 ^ (prefixWord ++ tailWord_1003774).sum := by decide
  have hdescent : baseEnd_1003774 < baseStart_1003774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003787 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 4, 3]
def baseStart_1003787 : Nat := 118140960795 + 1003787 * 2 ^ 59
def prefixEnd_1003787 : Nat := 4983230072969 + 3 ^ 40 * 1003787 * 2
def baseEnd_1003787 : Nat := 343616803823179608297449

theorem tailTrace_1003787 : CollatzResearch.WordTrace tailWord_1003787 prefixEnd_1003787 343616803823179608297449 := by
  unfold tailWord_1003787
  simp only [CollatzResearch.WordTrace]
  refine ⟨36611119614458607016217615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24407413076305738010811743 36611119614458607016217615)
  ·
    refine ⟨54916679421687910524326423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36611119614458607016217615 54916679421687910524326423)
    ·
      refine ⟨82375019132531865786489635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54916679421687910524326423 82375019132531865786489635)
      ·
        refine ⟨123562528698797798679734453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82375019132531865786489635 123562528698797798679734453)
        ·
          refine ⟨11583987065512293626225105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123562528698797798679734453 11583987065512293626225105)
          ·
            refine ⟨8687990299134220219668829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11583987065512293626225105 8687990299134220219668829)
            ·
              refine ⟨3257996362175332582375811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8687990299134220219668829 3257996362175332582375811)
              ·
                refine ⟨4886994543262998873563717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3257996362175332582375811 4886994543262998873563717)
                ·
                  refine ⟨916311476861812288793197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4886994543262998873563717 916311476861812288793197)
                  ·
                    refine ⟨343616803823179608297449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 916311476861812288793197 343616803823179608297449)
                    ·
                      rfl

theorem cell22_1003787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 3].length) (baseStart_1003787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003787 prefixEnd_1003787 := by exact prefixLift 1003787
  have htrace : WordTrace (prefixWord ++ tailWord_1003787) baseStart_1003787 baseEnd_1003787 := by
    simpa [prefixWord, tailWord_1003787, baseEnd_1003787] using wordTrace_append hprefix tailTrace_1003787
  have hstable : (prefixWord ++ tailWord_1003787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003787).length < 2 ^ (prefixWord ++ tailWord_1003787).sum := by decide
  have hdescent : baseEnd_1003787 < baseStart_1003787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003800 : List Nat := [2, 1, 2, 3, 1, 2, 2, 9]
def baseStart_1003800 : Nat := 118140960795 + 1003800 * 2 ^ 59
def prefixEnd_1003800 : Nat := 4983230072969 + 3 ^ 40 * 1003800 * 2
def baseEnd_1003800 : Nat := 38180139332094656413601

theorem tailTrace_1003800 : CollatzResearch.WordTrace tailWord_1003800 prefixEnd_1003800 38180139332094656413601 := by
  unfold tailWord_1003800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18305796881705755118220427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24407729175607673490960569 18305796881705755118220427)
  ·
    refine ⟨27458695322558632677330641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18305796881705755118220427 27458695322558632677330641)
    ·
      refine ⟨20594021491918974507997981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27458695322558632677330641 20594021491918974507997981)
      ·
        refine ⟨7722758059469615440499243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20594021491918974507997981 7722758059469615440499243)
        ·
          refine ⟨11584137089204423160748865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722758059469615440499243 11584137089204423160748865)
          ·
            refine ⟨8688102816903317370561649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11584137089204423160748865 8688102816903317370561649)
            ·
              refine ⟨6516077112677488027921237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8688102816903317370561649 6516077112677488027921237)
              ·
                refine ⟨38180139332094656413601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6516077112677488027921237 38180139332094656413601)
                ·
                  rfl

theorem cell22_1003800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 9].length) (baseStart_1003800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003800 prefixEnd_1003800 := by exact prefixLift 1003800
  have htrace : WordTrace (prefixWord ++ tailWord_1003800) baseStart_1003800 baseEnd_1003800 := by
    simpa [prefixWord, tailWord_1003800, baseEnd_1003800] using wordTrace_append hprefix tailTrace_1003800
  have hstable : (prefixWord ++ tailWord_1003800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003800).length < 2 ^ (prefixWord ++ tailWord_1003800).sum := by decide
  have hdescent : baseEnd_1003800 < baseStart_1003800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003832 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 5, 3]
def baseStart_1003832 : Nat := 118140960795 + 1003832 * 2 ^ 59
def prefixEnd_1003832 : Nat := 4983230072969 + 3 ^ 40 * 1003832 * 2
def baseEnd_1003832 : Nat := 343632208242814490922311

theorem tailTrace_1003832 : CollatzResearch.WordTrace tailWord_1003832 prefixEnd_1003832 343632208242814490922311 := by
  unfold tailWord_1003832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306380449647789850802875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24408507266197053134403833 18306380449647789850802875)
  ·
    refine ⟨27459570674471684776204313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18306380449647789850802875 27459570674471684776204313)
    ·
      refine ⟨20594678005853763582153235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27459570674471684776204313 20594678005853763582153235)
      ·
        refine ⟨30892017008780645373229853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20594678005853763582153235 30892017008780645373229853)
        ·
          refine ⟨11584506378292742014961195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30892017008780645373229853 11584506378292742014961195)
          ·
            refine ⟨17376759567439113022441793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584506378292742014961195 17376759567439113022441793)
            ·
              refine ⟨13032569675579334766831345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17376759567439113022441793 13032569675579334766831345)
              ·
                refine ⟨9774427256684501075123509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13032569675579334766831345 9774427256684501075123509)
                ·
                  refine ⟨916352555314171975792829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9774427256684501075123509 916352555314171975792829)
                  ·
                    refine ⟨343632208242814490922311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 916352555314171975792829 343632208242814490922311)
                    ·
                      rfl

theorem cell22_1003832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_1003832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003832 prefixEnd_1003832 := by exact prefixLift 1003832
  have htrace : WordTrace (prefixWord ++ tailWord_1003832) baseStart_1003832 baseEnd_1003832 := by
    simpa [prefixWord, tailWord_1003832, baseEnd_1003832] using wordTrace_append hprefix tailTrace_1003832
  have hstable : (prefixWord ++ tailWord_1003832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003832).length < 2 ^ (prefixWord ++ tailWord_1003832).sum := by decide
  have hdescent : baseEnd_1003832 < baseStart_1003832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003943 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1003943 : Nat := 118140960795 + 1003943 * 2 ^ 59
def prefixEnd_1003943 : Nat := 4983230072969 + 3 ^ 40 * 1003943 * 2
def baseEnd_1003943 : Nat := 343670205811247201396971

theorem tailTrace_1003943 : CollatzResearch.WordTrace tailWord_1003943 prefixEnd_1003943 343670205811247201396971 := by
  unfold tailWord_1003943
  simp only [CollatzResearch.WordTrace]
  refine ⟨36616809401893445658896483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24411206267928963772597655 36616809401893445658896483)
  ·
    refine ⟨54925214102840168488344725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36616809401893445658896483 54925214102840168488344725)
    ·
      refine ⟨2574619411070632897891159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54925214102840168488344725 2574619411070632897891159)
      ·
        refine ⟨3861929116605949346836739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574619411070632897891159 3861929116605949346836739)
        ·
          refine ⟨5792893674908924020255109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861929116605949346836739 5792893674908924020255109)
          ·
            refine ⟨1086167564045423253797833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5792893674908924020255109 1086167564045423253797833)
            ·
              refine ⟨814625673034067440348375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086167564045423253797833 814625673034067440348375)
              ·
                refine ⟨1221938509551101160522563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814625673034067440348375 1221938509551101160522563)
                ·
                  refine ⟨1832907764326651740783845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221938509551101160522563 1832907764326651740783845)
                  ·
                    refine ⟨343670205811247201396971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1832907764326651740783845 343670205811247201396971)
                    ·
                      rfl

theorem cell22_1003943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1003943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003943 prefixEnd_1003943 := by exact prefixLift 1003943
  have htrace : WordTrace (prefixWord ++ tailWord_1003943) baseStart_1003943 baseEnd_1003943 := by
    simpa [prefixWord, tailWord_1003943, baseEnd_1003943] using wordTrace_append hprefix tailTrace_1003943
  have hstable : (prefixWord ++ tailWord_1003943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003943).length < 2 ^ (prefixWord ++ tailWord_1003943).sum := by decide
  have hdescent : baseEnd_1003943 < baseStart_1003943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003986 : List Nat := [3, 2, 2, 4, 1, 1, 1, 8]
def baseStart_1003986 : Nat := 118140960795 + 1003986 * 2 ^ 59
def prefixEnd_1003986 : Nat := 4983230072969 + 3 ^ 40 * 1003986 * 2
def baseEnd_1003986 : Nat := 38187213954445491396871

theorem tailTrace_1003986 : CollatzResearch.WordTrace tailWord_1003986 prefixEnd_1003986 38187213954445491396871 := by
  unfold tailWord_1003986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154594435184416000677953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24412251827158442668474541 9154594435184416000677953)
  ·
    refine ⟨6865945826388312000508465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9154594435184416000677953 6865945826388312000508465)
    ·
      refine ⟨5149459369791234000381349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6865945826388312000508465 5149459369791234000381349)
      ·
        refine ⟨965523631835856375071503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5149459369791234000381349 965523631835856375071503)
        ·
          refine ⟨1448285447753784562607255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965523631835856375071503 1448285447753784562607255)
          ·
            refine ⟨2172428171630676843910883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448285447753784562607255 2172428171630676843910883)
            ·
              refine ⟨3258642257446015265866325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172428171630676843910883 3258642257446015265866325)
              ·
                refine ⟨38187213954445491396871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3258642257446015265866325 38187213954445491396871)
                ·
                  rfl

theorem cell22_1003986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_1003986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1003986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1003986 prefixEnd_1003986 := by exact prefixLift 1003986
  have htrace : WordTrace (prefixWord ++ tailWord_1003986) baseStart_1003986 baseEnd_1003986 := by
    simpa [prefixWord, tailWord_1003986, baseEnd_1003986] using wordTrace_append hprefix tailTrace_1003986
  have hstable : (prefixWord ++ tailWord_1003986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003986).length < 2 ^ (prefixWord ++ tailWord_1003986).sum := by decide
  have hdescent : baseEnd_1003986 < baseStart_1003986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004014 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1004014 : Nat := 118140960795 + 1004014 * 2 ^ 59
def prefixEnd_1004014 : Nat := 4983230072969 + 3 ^ 40 * 1004014 * 2
def baseEnd_1004014 : Nat := 114564836854075560957251

theorem tailTrace_1004014 : CollatzResearch.WordTrace tailWord_1004014 prefixEnd_1004014 114564836854075560957251 := by
  unfold tailWord_1004014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577424873079528098091387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24412932656424149856487397 4577424873079528098091387)
  ·
    refine ⟨6866137309619292147137081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577424873079528098091387 6866137309619292147137081)
    ·
      refine ⟨5149602982214469110352811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6866137309619292147137081 5149602982214469110352811)
      ·
        refine ⟨7724404473321703665529217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5149602982214469110352811 7724404473321703665529217)
        ·
          refine ⟨5793303354991277749146913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7724404473321703665529217 5793303354991277749146913)
          ·
            refine ⟨4344977516243458311860185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5793303354991277749146913 4344977516243458311860185)
            ·
              refine ⟨3258733137182593733895139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4344977516243458311860185 3258733137182593733895139)
              ·
                refine ⟨4888099705773890600842709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258733137182593733895139 4888099705773890600842709)
                ·
                  refine ⟨114564836854075560957251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4888099705773890600842709 114564836854075560957251)
                  ·
                    rfl

theorem cell22_1004014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1004014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004014 prefixEnd_1004014 := by exact prefixLift 1004014
  have htrace : WordTrace (prefixWord ++ tailWord_1004014) baseStart_1004014 baseEnd_1004014 := by
    simpa [prefixWord, tailWord_1004014, baseEnd_1004014] using wordTrace_append hprefix tailTrace_1004014
  have hstable : (prefixWord ++ tailWord_1004014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004014).length < 2 ^ (prefixWord ++ tailWord_1004014).sum := by decide
  have hdescent : baseEnd_1004014 < baseStart_1004014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004089 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_1004089 : Nat := 118140960795 + 1004089 * 2 ^ 59
def prefixEnd_1004089 : Nat := 4983230072969 + 3 ^ 40 * 1004089 * 2
def baseEnd_1004089 : Nat := 343720184594951487246523

theorem tailTrace_1004089 : CollatzResearch.WordTrace tailWord_1004089 prefixEnd_1004089 343720184594951487246523 := by
  unfold tailWord_1004089
  simp only [CollatzResearch.WordTrace]
  refine ⟨36622134459364512593711321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24414756306243008395807547 36622134459364512593711321)
  ·
    refine ⟨27466600844523384445283491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36622134459364512593711321 27466600844523384445283491)
    ·
      refine ⟨41199901266785076667925237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27466600844523384445283491 41199901266785076667925237)
      ·
        refine ⟨3862490743761100937617991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41199901266785076667925237 3862490743761100937617991)
        ·
          refine ⟨5793736115641651406426987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862490743761100937617991 5793736115641651406426987)
          ·
            refine ⟨8690604173462477109640481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793736115641651406426987 8690604173462477109640481)
            ·
              refine ⟨6517953130096857832230361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8690604173462477109640481 6517953130096857832230361)
              ·
                refine ⟨4888464847572643374172771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6517953130096857832230361 4888464847572643374172771)
                ·
                  refine ⟨7332697271358965061259157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888464847572643374172771 7332697271358965061259157)
                  ·
                    refine ⟨343720184594951487246523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7332697271358965061259157 343720184594951487246523)
                    ·
                      rfl

theorem cell22_1004089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_1004089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004089 prefixEnd_1004089 := by exact prefixLift 1004089
  have htrace : WordTrace (prefixWord ++ tailWord_1004089) baseStart_1004089 baseEnd_1004089 := by
    simpa [prefixWord, tailWord_1004089, baseEnd_1004089] using wordTrace_append hprefix tailTrace_1004089
  have hstable : (prefixWord ++ tailWord_1004089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004089).length < 2 ^ (prefixWord ++ tailWord_1004089).sum := by decide
  have hdescent : baseEnd_1004089 < baseStart_1004089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004106 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_1004106 : Nat := 118140960795 + 1004106 * 2 ^ 59
def prefixEnd_1004106 : Nat := 4983230072969 + 3 ^ 40 * 1004106 * 2
def baseEnd_1004106 : Nat := 343726004042369109571471

theorem tailTrace_1004106 : CollatzResearch.WordTrace tailWord_1004106 prefixEnd_1004106 343726004042369109571471 := by
  unfold tailWord_1004106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155688625075731124270043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24415169666868616331386781 9155688625075731124270043)
  ·
    refine ⟨13733532937613596686405065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9155688625075731124270043 13733532937613596686405065)
    ·
      refine ⟨10300149703210197514803799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13733532937613596686405065 10300149703210197514803799)
      ·
        refine ⟨15450224554815296272205699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10300149703210197514803799 15450224554815296272205699)
        ·
          refine ⟨23175336832222944408308549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15450224554815296272205699 23175336832222944408308549)
          ·
            refine ⟨4345375656041802076557853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23175336832222944408308549 4345375656041802076557853)
            ·
              refine ⟨1629515871015675778709195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4345375656041802076557853 1629515871015675778709195)
              ·
                refine ⟨2444273806523513668063793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629515871015675778709195 2444273806523513668063793)
                ·
                  refine ⟨1833205354892635251047845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2444273806523513668063793 1833205354892635251047845)
                  ·
                    refine ⟨343726004042369109571471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1833205354892635251047845 343726004042369109571471)
                    ·
                      rfl

theorem cell22_1004106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_1004106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004106 prefixEnd_1004106 := by exact prefixLift 1004106
  have htrace : WordTrace (prefixWord ++ tailWord_1004106) baseStart_1004106 baseEnd_1004106 := by
    simpa [prefixWord, tailWord_1004106, baseEnd_1004106] using wordTrace_append hprefix tailTrace_1004106
  have hstable : (prefixWord ++ tailWord_1004106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004106).length < 2 ^ (prefixWord ++ tailWord_1004106).sum := by decide
  have hdescent : baseEnd_1004106 < baseStart_1004106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004196 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1004196 : Nat := 118140960795 + 1004196 * 2 ^ 59
def prefixEnd_1004196 : Nat := 4983230072969 + 3 ^ 40 * 1004196 * 2
def baseEnd_1004196 : Nat := 343756812881638874821195

theorem tailTrace_1004196 : CollatzResearch.WordTrace tailWord_1004196 prefixEnd_1004196 343756812881638874821195 := by
  unfold tailWord_1004196
  simp only [CollatzResearch.WordTrace]
  refine ⟨18313018534988434933928221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24417358046651246578570961 18313018534988434933928221)
  ·
    refine ⟨6867381950620663100223083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18313018534988434933928221 6867381950620663100223083)
    ·
      refine ⟨10301072925930994650334625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6867381950620663100223083 10301072925930994650334625)
      ·
        refine ⟨7725804694448245987750969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10301072925930994650334625 7725804694448245987750969)
        ·
          refine ⟨5794353520836184490813227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7725804694448245987750969 5794353520836184490813227)
          ·
            refine ⟨8691530281254276736219841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794353520836184490813227 8691530281254276736219841)
            ·
              refine ⟨6518647710940707552164881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691530281254276736219841 6518647710940707552164881)
              ·
                refine ⟨4888985783205530664123661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6518647710940707552164881 4888985783205530664123661)
                ·
                  refine ⟨1833369668702073999046373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4888985783205530664123661 1833369668702073999046373)
                  ·
                    refine ⟨343756812881638874821195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1833369668702073999046373 343756812881638874821195)
                    ·
                      rfl

theorem cell22_1004196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1004196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004196 prefixEnd_1004196 := by exact prefixLift 1004196
  have htrace : WordTrace (prefixWord ++ tailWord_1004196) baseStart_1004196 baseEnd_1004196 := by
    simpa [prefixWord, tailWord_1004196, baseEnd_1004196] using wordTrace_append hprefix tailTrace_1004196
  have hstable : (prefixWord ++ tailWord_1004196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004196).length < 2 ^ (prefixWord ++ tailWord_1004196).sum := by decide
  have hdescent : baseEnd_1004196 < baseStart_1004196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004213 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1004213 : Nat := 118140960795 + 1004213 * 2 ^ 59
def prefixEnd_1004213 : Nat := 4983230072969 + 3 ^ 40 * 1004213 * 2
def baseEnd_1004213 : Nat := 343762632329056497146143

theorem tailTrace_1004213 : CollatzResearch.WordTrace tailWord_1004213 prefixEnd_1004213 343762632329056497146143 := by
  unfold tailWord_1004213
  simp only [CollatzResearch.WordTrace]
  refine ⟨36626657110915281771225293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24417771407276854514150195 36626657110915281771225293)
  ·
    refine ⟨13734996416593230664209485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36626657110915281771225293 13734996416593230664209485)
    ·
      refine ⟨5150623656222461499078557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13734996416593230664209485 5150623656222461499078557)
      ·
        refine ⟨1931483871083423062154459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5150623656222461499078557 1931483871083423062154459)
        ·
          refine ⟨2897225806625134593231689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931483871083423062154459 2897225806625134593231689)
          ·
            refine ⟨2172919354968850944923767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897225806625134593231689 2172919354968850944923767)
            ·
              refine ⟨3259379032453276417385651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172919354968850944923767 3259379032453276417385651)
              ·
                refine ⟨4889068548679914626078477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259379032453276417385651 4889068548679914626078477)
                ·
                  refine ⟨1833400705754967984779429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4889068548679914626078477 1833400705754967984779429)
                  ·
                    refine ⟨343762632329056497146143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1833400705754967984779429 343762632329056497146143)
                    ·
                      rfl

theorem cell22_1004213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1004213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004213 prefixEnd_1004213 := by exact prefixLift 1004213
  have htrace : WordTrace (prefixWord ++ tailWord_1004213) baseStart_1004213 baseEnd_1004213 := by
    simpa [prefixWord, tailWord_1004213, baseEnd_1004213] using wordTrace_append hprefix tailTrace_1004213
  have hstable : (prefixWord ++ tailWord_1004213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004213).length < 2 ^ (prefixWord ++ tailWord_1004213).sum := by decide
  have hdescent : baseEnd_1004213 < baseStart_1004213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004241 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_1004241 : Nat := 118140960795 + 1004241 * 2 ^ 59
def prefixEnd_1004241 : Nat := 4983230072969 + 3 ^ 40 * 1004241 * 2
def baseEnd_1004241 : Nat := 343772217301273757446057

theorem tailTrace_1004241 : CollatzResearch.WordTrace tailWord_1004241 prefixEnd_1004241 343772217301273757446057 := by
  unfold tailWord_1004241
  simp only [CollatzResearch.WordTrace]
  refine ⟨36627678354813842553244577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24418452236542561702163051 36627678354813842553244577)
  ·
    refine ⟨27470758766110381914933433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36627678354813842553244577 27470758766110381914933433)
    ·
      refine ⟨20603069074582786436200075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27470758766110381914933433 20603069074582786436200075)
      ·
        refine ⟨30904603611874179654300113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20603069074582786436200075 30904603611874179654300113)
        ·
          refine ⟨23178452708905634740725085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30904603611874179654300113 23178452708905634740725085)
          ·
            refine ⟨8691919765839613027771907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23178452708905634740725085 8691919765839613027771907)
            ·
              refine ⟨13037879648759419541657861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691919765839613027771907 13037879648759419541657861)
              ·
                refine ⟨2444602434142391164060849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13037879648759419541657861 2444602434142391164060849)
                ·
                  refine ⟨1833451825606793373045637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2444602434142391164060849 1833451825606793373045637)
                  ·
                    refine ⟨343772217301273757446057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1833451825606793373045637 343772217301273757446057)
                    ·
                      rfl

theorem cell22_1004241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_1004241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004241 prefixEnd_1004241 := by exact prefixLift 1004241
  have htrace : WordTrace (prefixWord ++ tailWord_1004241) baseStart_1004241 baseEnd_1004241 := by
    simpa [prefixWord, tailWord_1004241, baseEnd_1004241] using wordTrace_append hprefix tailTrace_1004241
  have hstable : (prefixWord ++ tailWord_1004241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004241).length < 2 ^ (prefixWord ++ tailWord_1004241).sum := by decide
  have hdescent : baseEnd_1004241 < baseStart_1004241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004305 : List Nat := [1, 2, 2, 1, 1, 3, 4, 4, 1, 3]
def baseStart_1004305 : Nat := 118140960795 + 1004305 * 2 ^ 59
def prefixEnd_1004305 : Nat := 4983230072969 + 3 ^ 40 * 1004305 * 2
def baseEnd_1004305 : Nat := 343794125809198923845861

theorem tailTrace_1004305 : CollatzResearch.WordTrace tailWord_1004305 prefixEnd_1004305 343794125809198923845861 := by
  unfold tailWord_1004305
  simp only [CollatzResearch.WordTrace]
  refine ⟨36630012626581981483574369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24420008417721320989049579 36630012626581981483574369)
  ·
    refine ⟨27472509469936486112680777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36630012626581981483574369 27472509469936486112680777)
    ·
      refine ⟨20604382102452364584510583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27472509469936486112680777 20604382102452364584510583)
      ·
        refine ⟨30906573153678546876765875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20604382102452364584510583 30906573153678546876765875)
        ·
          refine ⟨46359859730517820315148813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30906573153678546876765875 46359859730517820315148813)
          ·
            refine ⟨17384947398944182618180805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46359859730517820315148813 17384947398944182618180805)
            ·
              refine ⟨3259677637302034240908901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17384947398944182618180805 3259677637302034240908901)
              ·
                refine ⟨611189556994131420170419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3259677637302034240908901 611189556994131420170419)
                ·
                  refine ⟨916784335491197130255629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611189556994131420170419 916784335491197130255629)
                  ·
                    refine ⟨343794125809198923845861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 916784335491197130255629 343794125809198923845861)
                    ·
                      rfl

theorem cell22_1004305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_1004305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004305 prefixEnd_1004305 := by exact prefixLift 1004305
  have htrace : WordTrace (prefixWord ++ tailWord_1004305) baseStart_1004305 baseEnd_1004305 := by
    simpa [prefixWord, tailWord_1004305, baseEnd_1004305] using wordTrace_append hprefix tailTrace_1004305
  have hstable : (prefixWord ++ tailWord_1004305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004305).length < 2 ^ (prefixWord ++ tailWord_1004305).sum := by decide
  have hdescent : baseEnd_1004305 < baseStart_1004305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004356 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1004356 : Nat := 118140960795 + 1004356 * 2 ^ 59
def prefixEnd_1004356 : Nat := 4983230072969 + 3 ^ 40 * 1004356 * 2
def baseEnd_1004356 : Nat := 343811584151451790820705

theorem tailTrace_1004356 : CollatzResearch.WordTrace tailWord_1004356 prefixEnd_1004356 343811584151451790820705 := by
  unfold tailWord_1004356
  simp only [CollatzResearch.WordTrace]
  refine ⟨18315936374698608596840461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24421248499598144795787281 18315936374698608596840461)
  ·
    refine ⟨6868476140511978223815173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18315936374698608596840461 6868476140511978223815173)
    ·
      refine ⟨1287839276345995916965345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6868476140511978223815173 1287839276345995916965345)
      ·
        refine ⟨965879457259496937724009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1287839276345995916965345 965879457259496937724009)
        ·
          refine ⟨724409592944622703293007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965879457259496937724009 724409592944622703293007)
          ·
            refine ⟨1086614389416934054939511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724409592944622703293007 1086614389416934054939511)
            ·
              refine ⟨1629921584125401082409267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086614389416934054939511 1629921584125401082409267)
              ·
                refine ⟨2444882376188101623613901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629921584125401082409267 2444882376188101623613901)
                ·
                  refine ⟨916830891070538108855213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2444882376188101623613901 916830891070538108855213)
                  ·
                    refine ⟨343811584151451790820705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 916830891070538108855213 343811584151451790820705)
                    ·
                      rfl

theorem cell22_1004356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1004356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004356 prefixEnd_1004356 := by exact prefixLift 1004356
  have htrace : WordTrace (prefixWord ++ tailWord_1004356) baseStart_1004356 baseEnd_1004356 := by
    simpa [prefixWord, tailWord_1004356, baseEnd_1004356] using wordTrace_append hprefix tailTrace_1004356
  have hstable : (prefixWord ++ tailWord_1004356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004356).length < 2 ^ (prefixWord ++ tailWord_1004356).sum := by decide
  have hdescent : baseEnd_1004356 < baseStart_1004356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004376 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1004376 : Nat := 118140960795 + 1004376 * 2 ^ 59
def prefixEnd_1004376 : Nat := 4983230072969 + 3 ^ 40 * 1004376 * 2
def baseEnd_1004376 : Nat := 343818430560178405320643

theorem tailTrace_1004376 : CollatzResearch.WordTrace tailWord_1004376 prefixEnd_1004376 343818430560178405320643 := by
  unfold tailWord_1004376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18316301104662380304704491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24421734806216507072939321 18316301104662380304704491)
  ·
    refine ⟨27474451656993570457056737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18316301104662380304704491 27474451656993570457056737)
    ·
      refine ⟨20605838742745177842792553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27474451656993570457056737 20605838742745177842792553)
      ·
        refine ⟨15454379057058883382094415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20605838742745177842792553 15454379057058883382094415)
        ·
          refine ⟨23181568585588325073141623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15454379057058883382094415 23181568585588325073141623)
          ·
            refine ⟨34772352878382487609712435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23181568585588325073141623 34772352878382487609712435)
            ·
              refine ⟨52158529317573731414568653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34772352878382487609712435 52158529317573731414568653)
              ·
                refine ⟨19559448494090149280463245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52158529317573731414568653 19559448494090149280463245)
                ·
                  refine ⟨7334793185283805980173717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19559448494090149280463245 7334793185283805980173717)
                  ·
                    refine ⟨343818430560178405320643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7334793185283805980173717 343818430560178405320643)
                    ·
                      rfl

theorem cell22_1004376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1004376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1004376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1004376 prefixEnd_1004376 := by exact prefixLift 1004376
  have htrace : WordTrace (prefixWord ++ tailWord_1004376) baseStart_1004376 baseEnd_1004376 := by
    simpa [prefixWord, tailWord_1004376, baseEnd_1004376] using wordTrace_append hprefix tailTrace_1004376
  have hstable : (prefixWord ++ tailWord_1004376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004376).length < 2 ^ (prefixWord ++ tailWord_1004376).sum := by decide
  have hdescent : baseEnd_1004376 < baseStart_1004376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
