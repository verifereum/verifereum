Theory vfmTest0513[no_sig_docs]
Ancestors vfmTestDefs0513
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0513_0.nsv", "result0513_1.nsv"];
val thyn = "vfmTestDefs0513";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
