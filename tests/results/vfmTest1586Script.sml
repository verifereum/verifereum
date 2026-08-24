Theory vfmTest1586[no_sig_docs]
Ancestors vfmTestDefs1586
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1586_0.nsv"];
val thyn = "vfmTestDefs1586";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
