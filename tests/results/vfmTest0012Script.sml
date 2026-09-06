Theory vfmTest0012[no_sig_docs]
Ancestors vfmTestDefs0012
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0012_0.nsv", "result0012_1.nsv", "result0012_2.nsv", "result0012_3.nsv", "result0012_4.nsv", "result0012_5.nsv", "result0012_6.nsv", "result0012_7.nsv", "result0012_8.nsv", "result0012_9.nsv", "result0012_10.nsv", "result0012_11.nsv", "result0012_12.nsv", "result0012_13.nsv", "result0012_14.nsv", "result0012_15.nsv", "result0012_16.nsv", "result0012_17.nsv"];
val thyn = "vfmTestDefs0012";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
