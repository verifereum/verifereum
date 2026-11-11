Theory vfmTest0558[no_sig_docs]
Ancestors vfmTestDefs0558
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0558_0.nsv", "result0558_1.nsv", "result0558_2.nsv", "result0558_3.nsv", "result0558_4.nsv", "result0558_5.nsv", "result0558_6.nsv", "result0558_7.nsv"];
val thyn = "vfmTestDefs0558";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
