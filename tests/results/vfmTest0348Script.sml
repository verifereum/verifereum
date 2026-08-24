Theory vfmTest0348[no_sig_docs]
Ancestors vfmTestDefs0348
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0348_0.nsv", "result0348_1.nsv"];
val thyn = "vfmTestDefs0348";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
