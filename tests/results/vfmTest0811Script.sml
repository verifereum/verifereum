Theory vfmTest0811[no_sig_docs]
Ancestors vfmTestDefs0811
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0811_0.nsv", "result0811_1.nsv"];
val thyn = "vfmTestDefs0811";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
