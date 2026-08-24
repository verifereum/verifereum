Theory vfmTest2058[no_sig_docs]
Ancestors vfmTestDefs2058
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2058_0.nsv"];
val thyn = "vfmTestDefs2058";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
