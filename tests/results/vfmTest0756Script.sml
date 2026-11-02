Theory vfmTest0756[no_sig_docs]
Ancestors vfmTestDefs0756
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0756_0.nsv", "result0756_1.nsv", "result0756_2.nsv", "result0756_3.nsv", "result0756_4.nsv", "result0756_5.nsv", "result0756_6.nsv", "result0756_7.nsv"];
val thyn = "vfmTestDefs0756";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
