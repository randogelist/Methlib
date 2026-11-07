import SubmissionData

set_option autoImplicit false
namespace SubmissionEvidence

theorem encloses :
    SubmissionData.moments.Encloses SubmissionData.degree := by
  change Tail16Frontier.firstMomentData.Encloses 1
  exact Tail16Frontier.firstMomentData_encloses

end SubmissionEvidence

