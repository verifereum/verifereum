Theory vfmTest0969[no_sig_docs]
Ancestors vfmTestDefs0969
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0969_0.nsv", "result0969_1.nsv", "result0969_2.nsv", "result0969_3.nsv", "result0969_4.nsv", "result0969_5.nsv", "result0969_6.nsv", "result0969_7.nsv", "result0969_8.nsv", "result0969_9.nsv"];
val thyn = "vfmTestDefs0969";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
