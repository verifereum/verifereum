Theory vfmTest0056[no_sig_docs]
Ancestors vfmTestDefs0056
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0056_0.nsv", "result0056_1.nsv", "result0056_2.nsv", "result0056_3.nsv", "result0056_4.nsv", "result0056_5.nsv"];
val thyn = "vfmTestDefs0056";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
