Theory vfmTest0974[no_sig_docs]
Ancestors vfmTestDefs0974
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0974_0.nsv", "result0974_1.nsv", "result0974_2.nsv", "result0974_3.nsv", "result0974_4.nsv", "result0974_5.nsv", "result0974_6.nsv", "result0974_7.nsv", "result0974_8.nsv", "result0974_9.nsv", "result0974_10.nsv", "result0974_11.nsv", "result0974_12.nsv", "result0974_13.nsv"];
val thyn = "vfmTestDefs0974";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
