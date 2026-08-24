Theory vfmTest0008[no_sig_docs]
Ancestors vfmTestDefs0008
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0008_0.nsv", "result0008_1.nsv"];
val thyn = "vfmTestDefs0008";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
