Theory vfmTest0016[no_sig_docs]
Ancestors vfmTestDefs0016
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0016_0.nsv", "result0016_1.nsv", "result0016_2.nsv", "result0016_3.nsv"];
val thyn = "vfmTestDefs0016";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
