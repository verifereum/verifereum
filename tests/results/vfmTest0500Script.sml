Theory vfmTest0500[no_sig_docs]
Ancestors vfmTestDefs0500
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0500_0.nsv", "result0500_1.nsv"];
val thyn = "vfmTestDefs0500";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
