// box3d's motor joint definition and cydonia's createMouseJoint, whose code differed
// with the names of the temporaries generated before it
module mouse;

struct b3Vec3 { float x = 0, y = 0, z = 0; }
struct b3Quat { b3Vec3 v; float s = 1; }
struct b3Transform { b3Vec3 p; b3Quat q; }
struct b3WorldId { ushort index1; ushort generation; }
struct b3BodyId { int index1; ushort world0; ushort generation; }
struct b3JointId { int index1; ushort world0; ushort generation; }
struct b3JointDef
{
    void* userData;
    b3BodyId bodyIdA;
    b3BodyId bodyIdB;
    b3Transform localFrameA;
    b3Transform localFrameB;
    float forceThreshold = 0, torqueThreshold = 0, constraintHertz = 0, constraintDampingRatio = 0, drawScale = 0;
    bool collideConnected;
    int internalValue;
}
struct b3MotorJointDef
{
    b3JointDef base;
    b3Vec3 linearVelocity;
    float maxVelocityForce = 0;
    b3Vec3 angularVelocity;
    float maxVelocityTorque = 0, linearHertz = 0, linearDampingRatio = 0, maxSpringForce = 0,
        angularHertz = 0, angularDampingRatio = 0, maxSpringTorque = 0;
}
extern (C) b3MotorJointDef b3DefaultMotorJointDef();
extern (C) b3Vec3 b3Body_GetLocalPoint(b3BodyId, b3Vec3);
extern (C) b3Quat b3Body_GetRotation(b3BodyId);
extern (C) b3JointId b3CreateMotorJoint(b3WorldId, const b3MotorJointDef*);

pragma(inline, true) b3Vec3 b3Cross(b3Vec3 a, b3Vec3 b)
    => b3Vec3(a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x);
pragma(inline, true) b3Vec3 b3MulAdd(b3Vec3 a, float s, b3Vec3 b) => b3Vec3(a.x + s * b.x, a.y + s * b.y, a.z + s * b.z);
pragma(inline, true) b3Vec3 b3MulSub(b3Vec3 a, float s, b3Vec3 b) => b3Vec3(a.x - s * b.x, a.y - s * b.y, a.z - s * b.z);
pragma(inline, true) float b3Dot(b3Vec3 a, b3Vec3 b) => a.x * b.x + a.y * b.y + a.z * b.z;
pragma(inline, true) b3Quat b3InvMulQuat(b3Quat q1, b3Quat q2)
{
    immutable b3Vec3 t1 = b3Cross(q2.v, q1.v);
    immutable b3Vec3 t2 = b3MulAdd(t1, q1.s, q2.v);
    immutable b3Vec3 t3 = b3MulSub(t2, q2.s, q1.v);
    return b3Quat(t3, q1.s * q2.s + b3Dot(q1.v, q2.v));
}

struct Vec3 { float x = 0, y = 0, z = 0; }
struct Quat { float x = 0, y = 0, z = 0, w = 1; enum identity = Quat(0, 0, 0, 1); }
struct Body3D { b3BodyId id; }
struct Joint3D { b3JointId id; }
struct MotorJoint3D { Joint3D joint; }

b3Vec3 toB3(Vec3 v) => b3Vec3(v.x, v.y, v.z);
b3Quat toB3(Quat q) => b3Quat(b3Vec3(q.x, q.y, q.z), q.w);

private b3Transform jointFrame(Body3D body, Vec3 worldAnchor, Quat worldRot) @trusted
{
    b3Transform f;
    f.p = b3Body_GetLocalPoint(body.id, toB3(worldAnchor));
    f.q = b3InvMulQuat(b3Body_GetRotation(body.id), toB3(worldRot));
    return f;
}

private void wireBase(ref b3JointDef base, Body3D a, Body3D b, b3Transform frameA,
        b3Transform frameB, bool collideConnected)
{
    base.bodyIdA = a.id;
    base.bodyIdB = b.id;
    base.localFrameA = frameA;
    base.localFrameB = frameB;
    base.collideConnected = collideConnected;
}

MotorJoint3D createMouseJoint(b3WorldId world, Body3D ground, Body3D dragged,
        Vec3 grabPoint, float hertz = 5, float dampingRatio = 0.7f, float maxForce = 10000) @trusted
{
    auto def = b3DefaultMotorJointDef();
    wireBase(def.base, ground, dragged, jointFrame(ground, grabPoint,
            Quat.identity), jointFrame(dragged, grabPoint, Quat.identity), false);
    def.linearHertz = hertz;
    def.linearDampingRatio = dampingRatio;
    def.maxSpringForce = maxForce;
    return MotorJoint3D(Joint3D(b3CreateMotorJoint(world, &def)));
}
