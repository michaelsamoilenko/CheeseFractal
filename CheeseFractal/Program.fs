#if INTERACTIVE
#I @"C:\Program Files\Reference Assemblies\Microsoft\Framework\v3.0"
#r @"PresentationCore.dll"
#r @"PresentationFramework.dll"
#r @"WindowsBase.dll"
System.IO.Directory.SetCurrentDirectory(System.IO.Directory.GetCurrentDirectory() + "\CheeseFractal")
#endif

open System
open System.Windows
open System.Windows.Controls
open System.Windows.Markup
open System.Windows.Media
open System.Windows.Media.Media3D
open System.Xml

// ----------------------------------------------------------------------------------- //
// F# Types & Utilityfunctions

// Point in the 3D space
type Point3D = float * float * float

// 3D point represented using integers
type PointI3D = int * int * int

// Represents a triangle in 3D
type Triangle = Point3D * Point3D * Point3D

// Trianlge using integral points
type TriangleI = PointI3D * PointI3D * PointI3D

// Triangle represented using indices
type TriIndex = int * int * int

// Cross-product taking two lists as parameters
let cross_tup ls1 ls2 =
    ls2 |> List.map (fun el2 ->
        ls1 |> List.map (fun el1 -> (el1, el2))) |> List.concat


// Translate triangles
let translate (d:int * int * int) (pts:TriangleI list) : TriangleI list =
    let tpt (dx, dy, dz) ((x, y, z):PointI3D) = (x + dx, y + dy, z + dz)
    pts |> List.map (fun (pt1, pt2, pt3) ->
        (tpt d pt1, tpt d pt2, tpt d pt3))


// Converting grid with triangles to mesh
let to_mesh grid_size (trigs:TriangleI list) =
    let idx (x, y, z) = (((-z) * grid_size) + y) * grid_size + x
    trigs |> List.map (fun (p1, p2, p3) -> (idx p1, idx p2, idx p3))

// ----------------------------------------------------------------------------------- //
// Mesh representation

type Mesh =
    { Points : Point3D list;
      Triangles : TriIndex list; } with

    // Creates WPF mesh from F# 'mesh'
    member m.ToWpfMesh() =
        let ret = MeshGeometry3D()
        m.Points |> List.iter (fun (x,y,z) ->
            ret.Positions.Add(Point3D(x, y, z)))
        m.Triangles |> List.iter (fun (a,b,c) ->
            ret.TriangleIndices.Add(a)
            ret.TriangleIndices.Add(b)
            ret.TriangleIndices.Add(c))
        ret

// ----------------------------------------------------------------------------------- //
// Module that contains all supportingfunctions

module Internal =

    // Cube constructed using triangles -
    // first 'point' specifies the side of the cube and the rest is a list with
    // triangles to be rendered (so it is possible to easy filter relevant sides)
    let private initialCube : ((int * int * int) * TriangleI list) list =
        [ ( 1, 0, 0), [((1, 1, -1), (1, 1,    0), (1, 0, -1)); ((1, 1,    0), (1, 0,    0), (1, 0, -1)); ];     // right
            (-1, 0, 0), [((0, 1, -1), (0, 0, -1), (0, 1,    0)); ((0, 1,    0), (0, 0, -1), (0, 0,    0)); ];     // left
            ( 0, 0,-1), [((1, 1,    0), (0, 1,    0), (1, 0,    0)); ((0, 1,    0), (0, 0,    0), (1, 0,    0)); ];     // front
            ( 0, 0, 1), [((1, 1, -1), (1, 0, -1), (0, 1, -1)); ((0, 1, -1), (1, 0, -1), (0, 0, -1)); ];     // back
            ( 0, 1, 0), [((1, 1, -1), (0, 1, -1), (1, 1,    0)); ((0, 1, -1), (0, 1,    0), (1, 1,    0)); ];     // top
            ( 0,-1, 0), [((1, 0, -1), (1, 0,    0), (0, 0, -1)); ((0, 0, -1), (1, 0,    0), (0, 0,    0))    ]; ] // bottom

    // Returns a cube with filtered sides

    let private getCube inclSides =
        [ for side, trigs in initialCube do
            if Set.contains side inclSides then
                yield! trigs ]


    // Pattern that represents the fractal
    //        [ [1; 1; 1]; [1; 0; 1]; [1; 1; 1] ];
    //        [ [1; 0; 1]; [0; 0; 0]; [1; 0; 1] ];
    //        [ [1; 1; 1]; [1; 0; 1]; [1; 1; 1] ];
    //
    // Created using the following rule:
    //     when 2 or more from [x,y,z] equal 1 then return 0 otherwise 1
    let private addIfOne n m = if (n=1) then m+1 else m
    let private pattern = Array3D.init 3 3 3 (fun x y z ->
        let n = addIfOne x (addIfOne y (addIfOne z 0))
        if (n >= 2) then 0 else 1 )

    // Takes set representing included sides (around the current cube) and calls 'f'
    // for every sub-cube in the cube where pattern has '1', giving it coordinates
    // and set with sides to include in the cube
    let private patternMapi inclSides f =

        // Calculates set of sides to be included for specific location in the
        // pattern. Uses 'incl_sides' for lookup when testing border sides and
        // uses the pattern for sides inside the pattern.
        let getIncludedSides x y z =
            Set.ofSeq
                (seq
                    { // loop over all possible 'directions',
                        // test if out of range and use either pattern or 'incl_sides'
                        for idx, neq, (dx, dy, dz) in
                                [ (x, 0, (-1,0,0)); (y, 0, (0,-1,0)); (z, 0, (0,0,-1));
                                    (x, 2, ( 1,0,0)); (y, 2, (0, 1,0)); (z, 2, (0,0, 1)); ] do
                            if ((idx <> neq && pattern.[x+dx, y+dy, z+dz] = 0) ||
                                    (idx = neq    && Set.contains (dx, dy, dz) inclSides)) then yield (dx, dy, dz) })

        // Generate list with all sides
        [ for x in [0 .. 2] do
                for y in [0 .. 2] do
                    for z in [0 .. 2] do
                        if (pattern.[x,y,z] = 1) then
                            yield! f (x, y, z) (getIncludedSides x y z) ]

    // In the first step we want to include all six sides
    let private initSides =
        Set.ofSeq
            (seq { for i in [-1; 1] do
                     yield (i, 0, 0)
                     yield (0, i, 0)
                     yield (0, 0, i) })

    // Exported/public members...
    let InitSides = initSides
    let PatternMap = patternMapi
    let GetCube = getCube


// ----------------------------------------------------------------------------------- //
// Mainfunction for generating fractal recursively

let rec Generate k inclSides =
    if k = 1 then
        (Internal.GetCube inclSides)
    else
        let d = k/3
        Internal.PatternMap inclSides (fun (x, y, z) incl_sides ->
            (Generate d incl_sides) |> translate (x*d, y*d, -z*d)    )


// Number of repeats
// (on my machine it runs very slowly with 4, but it loads after some time..)
let Repeats = 3

// Creates mesh representing the fractal
let CreateFractal () =
    let threePow = int (Math.Pow (3.0, float Repeats))

    // Generate point coordinates
    let gridSize = threePow + 1
    let vec = [0.0 .. float (gridSize - 1)]    |> List.map (fun n ->
        n - (float (gridSize - 1)) / 2.0 )
    let mvec = vec |> List.map (fun n -> -n )
    let pts = (cross_tup (cross_tup vec vec) mvec) |> List.map (fun ((a, b), c) -> (a, b, c))

    // Generate cubes
    let cubes = Generate threePow Internal.InitSides

    // Build the mesh
    let fm = { Points = pts;    Triangles = to_mesh gridSize cubes; }
    (fm.Triangles.Length, fm.ToWpfMesh())

// ----------------------------------------------------------------------------------- //
// Create WPF window, set WPF properties, etc...

// Load window from XAML file
let CreateWindow (file : string) =
    use stream = XmlReader.Create(file)
    XamlReader.Load(stream) :?> Window

// Main - start the application
[<STAThread>]
do
    // create window
    let window = CreateWindow "fractal.xaml"
    let wp = window.FindName("view") :?> Viewport3D
    window.Content <- wp

    // create mesh in the window
    let br = SolidColorBrush()
    br.Color <- Color.FromRgb(255uy, 255uy, 255uy)
    let vis = window.FindName("fractal") :?> ModelVisual3D
    let trign, mesh = CreateFractal ()
    vis.Content <- GeometryModel3D(mesh, DiffuseMaterial(br))
    window.Title <- window.Title + String.Format(" (#triangles = {0})", trign)

    // run application
    let app = Application()
    window.Closed.Add(fun _ -> app.Shutdown(0))
    app.Run(window) |> ignore