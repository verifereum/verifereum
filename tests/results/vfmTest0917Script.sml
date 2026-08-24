Theory vfmTest0917[no_sig_docs]
Ancestors vfmTestDefs0917
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0917_0.nsv", "result0917_1.nsv", "result0917_2.nsv", "result0917_3.nsv", "result0917_4.nsv", "result0917_5.nsv", "result0917_6.nsv", "result0917_7.nsv", "result0917_8.nsv", "result0917_9.nsv", "result0917_10.nsv", "result0917_11.nsv"];
val thyn = "vfmTestDefs0917";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
