Theory vfmTest0523[no_sig_docs]
Ancestors vfmTestDefs0523
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0523_0.nsv", "result0523_1.nsv"];
val thyn = "vfmTestDefs0523";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
