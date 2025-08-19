
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

// File: contracts/interfaces/IUserIdentity.sol


pragma solidity ^0.8.20;

/**
 * @title IUserIdentity
 * @dev This interface defines the essential functions of the UserIdentity contract
 * that other contracts in the ecosystem need to interact with. It allows for
 * decoupled architecture, where contracts can communicate without having the full
 * source code of the other, preventing circular dependencies and improving modularity.
 */
interface IUserIdentity {
    /**
     * @dev A struct to hold all public-facing information about a user's profile.
     */
    struct UserProfile {
        address userAddress;      // The user's wallet address.
        string username;          // A unique, human-readable username.
        string skills;            // A string of user-defined skills, e.g., "Solidity,React,UI/UX".
        bytes ipfsPortfolioHash;  // An IPFS content identifier (CID) pointing to a JSON file with portfolio details.
        uint256 reputationScore;  // A numerical score representing the user's reputation.
        uint256 projectsCompleted; // A counter for successfully completed projects.
    }

    /**
     * @notice Updates the reputation score for a given user.
     * @dev This is a protected function that should only be callable by the authorized Reputation contract.
     * @param _user The address of the user whose score is being updated.
     * @param _newScore The user's newly calculated reputation score.
     */
    function updateReputation(address _user, uint256 _newScore) external;

    /**
     * @notice Increments the completed projects counter for a user.
     * @dev This is a protected function that should only be callable by an authorized contract
     *      (e.g., the Project contract upon successful completion).
     * @param _user The address of the user who completed a project.
     */
    function incrementProjectsCompleted(address _user) external;

    /**
     * @notice Fetches the full profile for a given user address.
     * @param _user The address of the user.
     * @return UserProfile A struct containing all of the user's profile data.
     */
    function getProfile(address _user) external view returns (UserProfile memory);
}
// File: contracts/core/UserIdentity.sol


pragma solidity ^0.8.20;


contract UserIdentity is Ownable {
    mapping(address => IUserIdentity.UserProfile) public profiles;
    mapping(string => address) private usernames;
    address public reputationContractAddress;
    address public projectAuthorityAddress;
    event ProfileCreated(address indexed user, string username);
    event ProfileUpdated(address indexed user);
    event AuthorizedContractSet(string indexed role, address indexed contractAddress);
    error UsernameTaken(string username);
    error UserNotFound(address user);
    error Unauthorized();
    constructor(address initialOwner) Ownable(initialOwner) {}
    modifier onlyAuthorized(address authority) { if (msg.sender != authority) revert Unauthorized(); _; }
    function createProfile(string memory _username, string memory _skills, bytes memory _ipfsPortfolioHash) external {
        if (profiles[msg.sender].userAddress != address(0)) revert("User already exists");
        if (usernames[_username] != address(0)) revert UsernameTaken(_username);
        profiles[msg.sender] = IUserIdentity.UserProfile({ userAddress: msg.sender, username: _username, skills: _skills, ipfsPortfolioHash: _ipfsPortfolioHash, reputationScore: 100, projectsCompleted: 0 });
        usernames[_username] = msg.sender;
        emit ProfileCreated(msg.sender, _username);
    }
    function updateProfile(string memory _skills, bytes memory _ipfsPortfolioHash) external {
        if (profiles[msg.sender].userAddress == address(0)) revert UserNotFound(msg.sender);
        profiles[msg.sender].skills = _skills;
        profiles[msg.sender].ipfsPortfolioHash = _ipfsPortfolioHash;
        emit ProfileUpdated(msg.sender);
    }
    function getProfile(address _user) external view returns (IUserIdentity.UserProfile memory) {
        if (profiles[_user].userAddress == address(0)) revert UserNotFound(_user);
        return profiles[_user];
    }
    function updateReputation(address _user, uint256 _newScore) external onlyAuthorized(reputationContractAddress) { profiles[_user].reputationScore = _newScore; }
    function incrementProjectsCompleted(address _user) external onlyAuthorized(projectAuthorityAddress) { profiles[_user].projectsCompleted++; }
    function setReputationContract(address _address) external onlyOwner { reputationContractAddress = _address; emit AuthorizedContractSet("Reputation", _address); }
    function setProjectAuthority(address _address) external onlyOwner { projectAuthorityAddress = _address; emit AuthorizedContractSet("ProjectAuthority", _address); }
}