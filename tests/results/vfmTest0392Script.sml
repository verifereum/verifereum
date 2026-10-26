Theory vfmTest0392[no_sig_docs]
Ancestors vfmTestDefs0392
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0392_0.nsv", "result0392_1.nsv", "result0392_2.nsv", "result0392_3.nsv", "result0392_4.nsv", "result0392_5.nsv", "result0392_6.nsv", "result0392_7.nsv", "result0392_8.nsv", "result0392_9.nsv", "result0392_10.nsv", "result0392_11.nsv"];
val thyn = "vfmTestDefs0392";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
