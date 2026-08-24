Theory vfmTest0308[no_sig_docs]
Ancestors vfmTestDefs0308
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0308_0.nsv", "result0308_1.nsv", "result0308_2.nsv"];
val thyn = "vfmTestDefs0308";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
