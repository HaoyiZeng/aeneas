use crate::my_std::{Arc, BTreeMap, RwLock, RwLockWriteGuard, Vec, Weak};

pub type CapabilityRef<T> = Arc<RwLock<Capability<T>>>;
pub type CapabilityWeak<T> = Weak<RwLock<Capability<T>>>;
pub type LocalHandle = u64;
pub type SubHandle = u64;

pub struct Capability<T> {
    pub owner: u64,
    pub sub_handle: SubHandle,
    pub next_sub_handle: SubHandle,

    // Capability type: MemoryRegion or Domain
    pub data: T,
    pub parent: CapabilityWeak<T>,
    pub children: Vec<CapabilityRef<T>>,
}

pub struct Domain {
    pub id: u64,
    pub policy: DomainPolicy,
    pub memory_capabilities: BTreeMap<LocalHandle, CapabilityWeak<MemoryRegion>>,
    pub domain_capabilities: BTreeMap<LocalHandle, CapabilityWeak<Domain>>,
}

pub fn generate_domain_id() -> u64 {
    todo!()
}

impl Domain {
    fn new(policy: DomainPolicy) -> Self {
        Domain {
            id: generate_domain_id(), // Placeholder, should be set appropriately
            policy,
            memory_capabilities: BTreeMap::new(),
            domain_capabilities: BTreeMap::new(),
        }
    }

    pub fn get_domain_capability(&self, handle: LocalHandle) -> Option<&CapabilityWeak<Domain>> {
        self.domain_capabilities.get(&handle)
    }

    pub fn get_memory_capability(
        &self,
        handle: LocalHandle,
    ) -> Option<&CapabilityWeak<MemoryRegion>> {
        self.memory_capabilities.get(&handle)
    }

    pub fn allocate_memory_handle(&self) -> LocalHandle {
        let mut handle: LocalHandle = 1;
        while self.memory_capabilities.contains_key(&handle) {
            handle += 1;
        }
        handle
    }

    pub fn add_memory_capability(
        &mut self,
        handle: LocalHandle,
        capa: CapabilityWeak<MemoryRegion>,
    ) {
        self.memory_capabilities.insert(handle, capa);
    }

    pub fn remove_memory_capability(
        &mut self,
        handle: LocalHandle,
    ) -> Option<CapabilityWeak<MemoryRegion>> {
        let result = self.memory_capabilities.remove(&handle);
        result
    }

    pub fn allocate_domain_handle(&self) -> LocalHandle {
        let mut handle: LocalHandle = 1;
        while self.domain_capabilities.contains_key(&handle) {
            handle += 1;
        }
        handle
    }

    pub fn add_domain_capability(&mut self, handle: LocalHandle, capa: CapabilityWeak<Domain>) {
        self.domain_capabilities.insert(handle, capa);
    }
}

pub struct DomainPolicy {
    pub lattice: bool,
}

impl DomainPolicy {
    pub fn is_subset_of(&self, parent: &DomainPolicy) -> Option<()> {
        if self.lattice <= parent.lattice {
            Some(())
        } else {
            None
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Access {
    pub start: u64,
    pub size: u64,
    pub rights: Rights,
}

impl Access {
    /// Create a new access descriptor
    pub fn new(start: u64, size: u64, rights: Rights) -> Self {
        Access {
            start,
            size,
            rights,
        }
    }

    pub fn end(&self) -> u64 {
        self.start + self.size
    }

    pub fn contained_in(&self, other: &Access) -> bool {
        self.start >= other.start && self.end() <= other.end()
    }

    pub fn overlaps(&self, other: &Access) -> bool {
        if self.end() <= other.start {
            false
        } else {
            self.start < other.end()
        }
    }

    pub fn rights_subset_of(&self, other: &Access) -> bool {
        self.rights.is_subset_of(&other.rights)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Rights {
    pub read: bool,
    pub write: bool,
    pub execute: bool,
}

impl Rights {
    pub fn is_subset_of(&self, other: &Rights) -> bool {
        (!self.read || other.read)
            && (!self.write || other.write)
            && (!self.execute || other.execute)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegionKind {
    Alias,
    Carve,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegionStatus {
    Exclusive,
    Aliased,
}

#[derive(Debug, Clone)]
pub struct MemoryRegion {
    pub kind: RegionKind,
    pub status: RegionStatus,
    pub access: Access,
}
impl MemoryRegion {
    pub fn alias(&self, access: Access) -> Option<Self> {
        // Validate access is within parent
        if !access.contained_in(&self.access) {
            return None;
        }

        // Validate rights are subset
        if !access.rights_subset_of(&self.access) {
            return None;
        }

        Some(MemoryRegion {
            kind: RegionKind::Alias,
            status: RegionStatus::Aliased,
            access,
        })
    }

    pub fn carve(&self, access: Access) -> Option<Self> {
        // Validate access is within parent
        if !access.contained_in(&self.access) {
            return None;
        }

        // Validate rights are subset
        if !access.rights_subset_of(&self.access) {
            return None;
        }

        // Carved child inherits parent's status
        Some(MemoryRegion {
            kind: RegionKind::Carve,
            status: self.status,
            access,
        })
    }
}

impl<T> Capability<T> {
    pub fn new_root(owner: u64, data: T, handle: SubHandle) -> CapabilityRef<T> {
        Arc::new(RwLock::new(Capability {
            owner,
            sub_handle: handle,
            next_sub_handle: 1,
            data,
            parent: Weak::new(),
            children: Vec::new(),
        }))
    }

    pub fn new_child(
        owner: u64,
        data: T,
        handle: SubHandle,
        parent: CapabilityWeak<T>,
    ) -> CapabilityRef<T> {
        Arc::new(RwLock::new(Capability {
            owner,
            sub_handle: handle,
            next_sub_handle: 1,
            data,
            parent,
            children: Vec::new(),
        }))
    }

    pub fn add_child(&mut self, child: CapabilityRef<T>) {
        self.children.push(child);
    }

    pub fn remove_child(&mut self, child_sub: SubHandle) -> Option<CapabilityRef<T>> {
        let mut pos = 0;
        while pos < self.children.len() {
            if self.children[pos].read().sub_handle == child_sub {
                return Some(self.children.remove(pos));
            }
            pos += 1;
        }
        None
    }

    pub fn get_parent(&self) -> Option<CapabilityRef<T>> {
        self.parent.upgrade()
    }

    pub fn has_parent(&self) -> bool {
        self.parent.strong_count() > 0
    }
}

impl Capability<MemoryRegion> {
    pub fn alias_child(
        parent_ref: &CapabilityRef<MemoryRegion>,
        access: Access,
        owner: u64,
    ) -> Option<CapabilityRef<MemoryRegion>> {
        let mut parent = parent_ref.write();

        // Check if the requested range overlaps with any existing carved children
        // Aliasing is not allowed to overlap with carved regions
        // for child_ref in &parent.children {
        for i in 0..parent.children.len() {
            let child_ref = &parent.children[i];
            let child = child_ref.read();
            if child.data.kind == RegionKind::Carve && access.overlaps(&child.data.access) {
                return None;
            }
        }

        let child_region = parent.data.alias(access)?;

        let sub_handle = parent.next_sub_handle;
        parent.next_sub_handle += 1;

        let child =
            Capability::new_child(owner, child_region, sub_handle, Arc::downgrade(parent_ref));

        parent.add_child(child.clone());

        Some(child)
    }

    pub fn carve_child(
        parent_ref: &CapabilityRef<MemoryRegion>,
        access: Access,
        owner: u64,
    ) -> Option<CapabilityRef<MemoryRegion>> {
        let mut parent = parent_ref.write();

        let mut child_index = 0;
        while child_index < parent.children.len() {
            let child = parent.children[child_index].read();
            if access.overlaps(&child.data.access) {
                return None;
            }
            child_index += 1;
        }

        let child_region = parent.data.carve(access)?;
        let sub_handle = parent.next_sub_handle;
        parent.next_sub_handle += 1;

        let child =
            Capability::new_child(owner, child_region, sub_handle, Arc::downgrade(parent_ref));
        parent.add_child(child.clone());

        Some(child)
    }

    // pub fn send_to(
    //     cap_ref: &CapabilityRef<MemoryRegion>,
    //     caller: u64,
    //     new_owner: u64,
    // ) -> Option<()>{
    //     { //verify the ownership under a read lock
    //         let capa = cap_ref.read();
    //         if capa.owner != caller {
    //             return None;
    //         }
    //         // capa.owned.validate_operation(MonitorAPI::SEND)?; WHAT IS THIS? --- IGNORE ---
    //     }

    //     let mut capa = cap_ref.write();

    //     // linearisability check
    //     if capa.owner != caller {
    //         return None;
    //     }

    //     capa.owner = new_owner;
    //     Some(())
    // }

    // pub fn revoke_child_ref(
    //     parent_ref: &CapabilityRef<MemoryRegion>,
    //     child_ref: &CapabilityRef<MemoryRegion>,
    // ) -> Option<()> {
    //     let child_sub = child_ref.read().handle;
    //     let mut parent = parent_ref.write();

    //     let child = parent.remove_child(child_sub)?;

    // // Drop parent lock before recursing
    //     drop(parent);

    //     // let update = &Self::revoke_asubtree(&child);
    //     // Some(update) --- IGNORE ---
    //     Some(())
    // }

    // pub fn revoke_child(
    //     parent_ref: &CapabilityRef<MemoryRegion>,
    //     child_sub: SubHandle,
    // ) -> Option<()> {
    //     let mut parent = parent_ref.write();

    //     let child = parent.remove_child(child_sub)?;

    //     drop(parent);

    //     // let update = &Self::revoke_asubtree(&child);
    //     // Some(update) --- IGNORE ---
    //     Some(())

    // }

    // pub fn revoke_subtree(capa_ref: &CapabilityRef<MemoryRegion>) {
    //     todo!()
    // }

    pub fn compute_view(&self) -> Vec<Access> {
        let mut view = Vec::new();
        view.push(self.data.access);

        for i in 0..self.children.len() {
            // for child_ref in &self.children {
            let child = self.children[i].read();
            if child.data.kind == RegionKind::Carve {
                view = Self::subtract_region(&view, &child.data.access);
            }
        }

        view
    }

    fn subtract_region(regions: &Vec<Access>, to_subtract: &Access) -> Vec<Access> {
        let mut result = Vec::new();

        let mut region_index = 0;
        while region_index < regions.len() {
            let region = &regions[region_index];
            if !region.overlaps(to_subtract) {
                result.push(*region);
            } else {
                if region.start < to_subtract.start {
                    result.push(Access::new(
                        region.start,
                        to_subtract.start - region.start,
                        region.rights,
                    ));
                }
                if region.end() > to_subtract.end() {
                    result.push(Access::new(
                        to_subtract.end(),
                        region.end() - to_subtract.end(),
                        region.rights,
                    ));
                }
            }
            region_index += 1;
        }

        result
    }
}

/// Acquire two domain write locks atomically in `DomainId` order.
///
/// Acquiring by increasing id gives a global total order on lock acquisition,
/// which rules out ABBA deadlock between any two concurrent two-domain
/// operations.  The two ids MUST differ (a self-pair would write-lock the same
/// non-reentrant `RwLock` twice and deadlock); callers guarantee this.
macro_rules! lock_two_domains_ordered {
    (
        let ($a_guard:ident, $b_guard:ident) =
            ($a_ref:expr, $a_id:expr, $b_ref:expr, $b_id:expr);
    ) => {
        debug_assert!(
            $a_id != $b_id,
            "lock_two_domains_ordered: same DomainId — would deadlock"
        );
        let (mut $a_guard, mut $b_guard) = if $a_id < $b_id {
            let a_w = $a_ref.write();
            let b_w = $b_ref.write();
            (a_w, b_w)
        } else {
            let b_w = $b_ref.write();
            let a_w = $a_ref.write();
            (a_w, b_w)
        };
    };
}

#[verify::stateful_lifetimes]
#[verify::opaque]
fn lock_two_domains_ordered<'a>(
    _a_ref: &'a CapabilityRef<Domain>,
    _a_id: u64,
    _b_ref: &'a CapabilityRef<Domain>,
    _b_id: u64,
) -> (
    RwLockWriteGuard<'a, Capability<Domain>>,
    RwLockWriteGuard<'a, Capability<Domain>>,
) {
    unimplemented!()
}

impl Capability<Domain> {
    pub fn create_child_domain(
        parent_cap: &mut Capability<Domain>,
        parent_ref: &CapabilityRef<Domain>,
        policy: DomainPolicy,
        owner: u64,
    ) -> Option<CapabilityRef<Domain>> {
        policy.is_subset_of(&parent_cap.data.policy)?;

        let child_domain = Domain::new(policy);

        // Auto-allocate a unique SubHandle from the parent's counter; capture depth too.
        let sub_handle = parent_cap.next_sub_handle;
        parent_cap.next_sub_handle += 1;

        let child =
            Capability::new_child(owner, child_domain, sub_handle, Arc::downgrade(parent_ref));

        parent_cap.add_child(child.clone());

        Some(child)
    }

    // pub fn revoke_child_domain(
    //     parent_ref: &CapabilityRef<Domain>,
    //     child_sub: SubHandle,
    // ) -> Option<()> {
    //     let mut parent = parent_ref.write();

    //     let child_ref = parent.remove_child(child_sub)?;

    //     let parent_id = parent.data.id;
    //     drop(parent);

    //     // let update = &Self::revoke_asubtree(&child, Some(parent_id))?;
    //     // Some(update) --- IGNORE ---
    //     Some(())
    // }

    // fn revoke_subtree(capa_ref: &CapabilityRef<Domain>, parent_id: Option<u64>) {
    //     todo!()
    // }

    /// Carve a memory sub-region.  Returns `(LocalHandle, SubHandle)`.
    ///
    /// - `LocalHandle`: the caller's domain-table key for the new child.
    /// - `SubHandle`: the child's stable tree identity (auto-allocated from the
    ///   source region's counter).  Pass this to [`revoke`] to
    ///   revoke the child even after it has been sent to another domain.
    pub fn carve(
        caller: &CapabilityRef<Domain>,
        region: LocalHandle,
        access: Access,
    ) -> Option<(LocalHandle, SubHandle)> {
        // Single-lock discipline: validate + mutate atomically under caller.write().
        // By the dom↔cap invariant (every cap in caller's memory table is owned by
        // caller), the old back-edge `region.owner == caller.id` re-check is redundant.
        // Lock order: caller.write() -> region.write() (taken inside carve_child).
        let mut w = caller.write();
        let owner_id = w.data.id;
        let region_ref = w.data.get_memory_capability(region)?.upgrade()?;

        let child_ref = Capability::carve_child(&region_ref, access, owner_id)?;
        let child_sub = child_ref.read().sub_handle;

        let new_handle = w.data.allocate_memory_handle();
        w.data
            .add_memory_capability(new_handle, Arc::downgrade(&child_ref));

        Some((new_handle, child_sub))
    }

    pub fn alias(
        caller: &CapabilityRef<Domain>,
        region: LocalHandle,
        access: Access,
    ) -> Option<(LocalHandle, SubHandle)> {
        // Single-lock discipline (see `carve`): validate + mutate under caller.write();
        // the dom↔cap invariant makes the back-edge owner re-check redundant.
        // Lock order: caller.write() -> region.write() (taken inside alias_child).
        let mut w = caller.write();
        let owner_id = w.data.id;
        let region_ref = w.data.get_memory_capability(region)?.upgrade()?;

        let child_ref = Capability::alias_child(&region_ref, access, owner_id)?;
        let child_sub = child_ref.read().sub_handle;

        let new_handle = w.data.allocate_memory_handle();
        w.data
            .add_memory_capability(new_handle, Arc::downgrade(&child_ref));

        Some((new_handle, child_sub))
    }

    pub fn send(
        caller: &CapabilityRef<Domain>,
        cap: LocalHandle,
        receiver: LocalHandle,
    ) -> Option<()> {
        // INV@: id uniqueness
        // Resolve the receiver Arc + id under a brief read. This is non-authoritative:
        // it only fixes which two locks to take and in what order. The authoritative
        // transfer happens below with both domain write locks held.
        let (caller_id, receiver_ref) = {
            let r = caller.read();
            let receiver_ref = r.data.get_domain_capability(receiver)?.upgrade()?;
            (r.data.id, receiver_ref)
        };
        let receiver_id = receiver_ref.read().data.id;

        // RwLock is non-reentrant: a self-send would write-lock the same domain
        // twice and deadlock. Reject it (precondition: caller_id != receiver_id).
        if caller_id == receiver_id {
            return None;
        }

        // Acquire both domain write locks in DomainId order (ABBA-safe).
        let (mut caller_w, mut receiver_w) =
            lock_two_domains_ordered(caller, caller_id, &receiver_ref, receiver_id);

        // `cap` is taken from caller's own table, so by the dom↔cap invariant it is
        // owned by caller — the old `owner == caller_id` re-check is redundant.
        let cap_weak = caller_w.data.remove_memory_capability(cap)?;
        let cap_ref = cap_weak.upgrade()?;

        cap_ref.write().owner = receiver_id;

        let new_handle = receiver_w.data.allocate_memory_handle();
        receiver_w
            .data
            .add_memory_capability(new_handle, Arc::downgrade(&cap_ref));

        Some(())
    }

    pub fn create(parent: &CapabilityRef<Domain>, policy: DomainPolicy) -> Option<LocalHandle> {
        let mut w = parent.write();
        let owner_id = w.data.id;
        let new_handler = w.data.allocate_domain_handle();
        let child_ref = Capability::create_child_domain(&mut *w, parent, policy, owner_id)?;
        w.data
            .add_domain_capability(new_handler, Arc::downgrade(&child_ref));

        Some(new_handler)
    }
}
