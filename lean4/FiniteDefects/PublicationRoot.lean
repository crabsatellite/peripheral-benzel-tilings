import FiniteDefects.DefectArithmetic
import FiniteDefects.OwnerDomainHierarchy

/-!
# Historical owner-domain compatibility root

This import path is retained for users of the earlier owner-boundary API.  The
combined publication root is `PeripheralBenzelPublication`; it imports the
literal exact-cover, finite-defect, bijection, enumeration, and generating-
function consumers audited for the current manuscript.
-/

namespace FiniteDefects

def publication_d3k_boundary_labels := @d3k_boundaryU_labels
def publication_d3k1_boundary_labels := @d3k1_boundaryU_labels
def publication_d3k_boundary_energy := @d3k_boundaryU_present_energy
def publication_d3k1_boundary_energy := @d3k1_boundaryU_present_energy
def publication_defects_d3k := @defects_d3k
def publication_defects_d3k1 := @defects_d3k1
def publication_owner_domain_d3k := @exists_ownerLabelPresentAtOffset_d3k
def publication_owner_domain_d3k1 := @exists_ownerLabelPresentAtOffset_d3k1
def publication_owner_domain_d3k2 := @all_ownerLabelsPresentAtOffset_d3k2
def publication_boundaryU_card := @card_boundaryU
def publication_boundaryV_card := @card_boundaryV
def publication_boundaryW_card := @card_boundaryW
def publication_removed_owner_card := @card_outsideTruncatedOwnerDomain
def publication_benzel_cell_has_owner := @benzel_cell_has_owner
def publication_owner_representation_unique := @owner_representation_unique
def publication_literal_owner_transport := @ownerLabelPresentAtOffset_iff_inBenzel
def publication_literal_owner_domain_d3k := @owner_meets_literal_benzel_d3k
def publication_literal_owner_domain_d3k1 := @owner_meets_literal_benzel_d3k1
def publication_literal_owner_domain_d3k2 := @owner_meets_literal_benzel_d3k2
def publication_literal_owner_labels_d3k2 := @owner_labels_literal_benzel_d3k2
def publication_d3k_boundaryU_literal_labels := @d3k_boundaryU_literal_labels
def publication_d3k_boundaryV_literal_labels := @d3k_boundaryV_literal_labels
def publication_d3k_boundaryW_literal_labels := @d3k_boundaryW_literal_labels
def publication_d3k1_boundaryU_literal_labels := @d3k1_boundaryU_literal_labels
def publication_d3k1_boundaryV_literal_labels := @d3k1_boundaryV_literal_labels
def publication_d3k1_boundaryW_literal_labels := @d3k1_boundaryW_literal_labels
def publication_owner_domain_hierarchy := ownerDomainHierarchyKernel

end FiniteDefects
