Theory vfmTest2708[no_sig_docs]
Ancestors vfmTestDefs2708
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2708_0.nsv", "result2708_1.nsv", "result2708_2.nsv", "result2708_3.nsv"];
val thyn = "vfmTestDefs2708";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
