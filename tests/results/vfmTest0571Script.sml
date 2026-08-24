Theory vfmTest0571[no_sig_docs]
Ancestors vfmTestDefs0571
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0571_0.nsv"];
val thyn = "vfmTestDefs0571";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
