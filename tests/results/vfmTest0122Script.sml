Theory vfmTest0122[no_sig_docs]
Ancestors vfmTestDefs0122
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0122_0.nsv", "result0122_1.nsv", "result0122_2.nsv", "result0122_3.nsv", "result0122_4.nsv", "result0122_5.nsv", "result0122_6.nsv", "result0122_7.nsv", "result0122_8.nsv"];
val thyn = "vfmTestDefs0122";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
