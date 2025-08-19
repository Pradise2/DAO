
// File: @openzeppelin/contracts/utils/Context.sol


// OpenZeppelin Contracts (last updated v5.0.1) (utils/Context.sol)

pragma solidity ^0.8.20;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

// File: @openzeppelin/contracts/access/Ownable.sol


// OpenZeppelin Contracts (last updated v5.0.0) (access/Ownable.sol)

pragma solidity ^0.8.20;


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * The initial owner is set to the address provided by the deployer. This can
 * later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    /**
     * @dev The caller account is not authorized to perform an operation.
     */
    error OwnableUnauthorizedAccount(address account);

    /**
     * @dev The owner is not a valid owner account. (eg. `address(0)`)
     */
    error OwnableInvalidOwner(address owner);

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the address provided by the deployer as the initial owner.
     */
    constructor(address initialOwner) {
        if (initialOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(initialOwner);
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        if (owner() != _msgSender()) {
            revert OwnableUnauthorizedAccount(_msgSender());
        }
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        if (newOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// File: @openzeppelin/contracts/token/ERC20/IERC20.sol


// OpenZeppelin Contracts (last updated v5.4.0) (token/ERC20/IERC20.sol)

pragma solidity >=0.4.16;

/**
 * @dev Interface of the ERC-20 standard as defined in the ERC.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the value of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the value of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 value) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the
     * allowance mechanism. `value` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 value) external returns (bool);
}

// File: contracts/core/Escrow.sol


pragma solidity ^0.8.20;

contract Escrow {
    enum EscrowState { AwaitingFunding, Funded, Released, Refunded, Locked }
    address public immutable depositor; address public immutable beneficiary; address public immutable token; uint256 public immutable amount;
    EscrowState public state; address public disputeResolver;
    event Funded(uint256 amount); event Released(address indexed to, uint256 amount); event Refunded(address indexed to, uint256 amount); event LockedForDispute(); event DisputeResolved(address winner);
    constructor(address _token, address _depositor, address _beneficiary, uint256 _amount) {
        token = _token; depositor = _depositor; beneficiary = _beneficiary; amount = _amount; state = EscrowState.AwaitingFunding;
    }
    function fund() external { require(state == EscrowState.AwaitingFunding, "Escrow: Not awaiting funds"); IERC20(token).transferFrom(depositor, address(this), amount); state = EscrowState.Funded; emit Funded(amount); }
    function release() external { require(msg.sender == depositor, "Escrow: Caller is not the depositor"); require(state == EscrowState.Funded, "Escrow: Not in a releasable state"); state = EscrowState.Released; IERC20(token).transfer(beneficiary, amount); emit Released(beneficiary, amount); }
    function lockForDispute() external { require(msg.sender == depositor || msg.sender == beneficiary, "Escrow: Not a party to the contract"); require(state == EscrowState.Funded, "Escrow: Can only lock funded escrow"); state = EscrowState.Locked; emit LockedForDispute(); }
    function resolveDispute(address winner) external { require(msg.sender == disputeResolver, "Escrow: Caller is not the dispute resolver"); require(state == EscrowState.Locked, "Escrow: Not locked for dispute"); if (winner == beneficiary) { state = EscrowState.Released; IERC20(token).transfer(beneficiary, amount); } else { state = EscrowState.Refunded; IERC20(token).transfer(depositor, amount); } emit DisputeResolved(winner); }
    function setDisputeResolver(address _resolver) external { require(msg.sender == depositor, "Escrow: Not depositor"); require(disputeResolver == address(0), "Escrow: Resolver already set"); disputeResolver = _resolver; }
}
// File: contracts/Governance/DisputeResolution.sol


pragma solidity ^0.8.20;


contract DisputeResolution is Ownable {
    enum DisputeStatus { Voting, Resolved } enum Verdict { Unresolved, ForPlaintiff, ForDefendant }
    struct Dispute { address escrowContract; address plaintiff; address defendant; uint plaintiffVotes; uint defendantVotes; DisputeStatus status; Verdict verdict; }
    mapping(address => bool) public isJuror; uint public disputeCount; mapping(uint => Dispute) public disputes; mapping(uint => mapping(address => bool)) public hasJurorVoted;
    event DisputeOpened(uint indexed disputeId, address indexed escrowContract); event VoteCast(uint indexed disputeId, address indexed juror, Verdict vote); event DisputeResolved(uint indexed disputeId, Verdict verdict);
    constructor(address _initialOwner) Ownable(_initialOwner) {}
    function openDispute(address _escrowContract, address _plaintiff, address _defendant) external onlyOwner {
        disputeCount++; uint id = disputeCount;
        disputes[id] = Dispute({ escrowContract: _escrowContract, plaintiff: _plaintiff, defendant: _defendant, plaintiffVotes: 0, defendantVotes: 0, status: DisputeStatus.Voting, verdict: Verdict.Unresolved });
        emit DisputeOpened(id, _escrowContract);
    }
    function castVote(uint _disputeId, Verdict _vote) external {
        require(isJuror[msg.sender], "Dispute: Not a juror"); Dispute storage dispute = disputes[_disputeId]; require(dispute.status == DisputeStatus.Voting, "Dispute: Voting not active"); require(!hasJurorVoted[_disputeId][msg.sender], "Dispute: Juror has already voted"); require(_vote == Verdict.ForPlaintiff || _vote == Verdict.ForDefendant, "Dispute: Invalid vote");
        if (_vote == Verdict.ForPlaintiff) { dispute.plaintiffVotes++; } else { dispute.defendantVotes++; }
        hasJurorVoted[_disputeId][msg.sender] = true; emit VoteCast(_disputeId, msg.sender, _vote);
    }
    function resolveDispute(uint _disputeId) external onlyOwner {
        Dispute storage dispute = disputes[_disputeId]; require(dispute.status == DisputeStatus.Voting, "Dispute: Not in voting");
        Verdict finalVerdict = (dispute.plaintiffVotes > dispute.defendantVotes) ? Verdict.ForPlaintiff : Verdict.ForDefendant;
        dispute.status = DisputeStatus.Resolved; dispute.verdict = finalVerdict;
        address winner = (finalVerdict == Verdict.ForPlaintiff) ? dispute.plaintiff : dispute.defendant;
        Escrow(dispute.escrowContract).resolveDispute(winner);
        emit DisputeResolved(_disputeId, finalVerdict);
    }
    function addJuror(address _juror) external onlyOwner { isJuror[_juror] = true; }
    function removeJuror(address _juror) external onlyOwner { isJuror[_juror] = false; }
}