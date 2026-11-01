Theory vfmTest0749[no_sig_docs]
Ancestors vfmTestDefs0749
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0749_0.nsv", "result0749_1.nsv", "result0749_2.nsv", "result0749_3.nsv", "result0749_4.nsv", "result0749_5.nsv", "result0749_6.nsv", "result0749_7.nsv", "result0749_8.nsv", "result0749_9.nsv", "result0749_10.nsv", "result0749_11.nsv"];
val thyn = "vfmTestDefs0749";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
