Theory vfmTest0671[no_sig_docs]
Ancestors vfmTestDefs0671
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0671_0.nsv", "result0671_1.nsv", "result0671_2.nsv", "result0671_3.nsv", "result0671_4.nsv", "result0671_5.nsv", "result0671_6.nsv", "result0671_7.nsv", "result0671_8.nsv", "result0671_9.nsv", "result0671_10.nsv", "result0671_11.nsv", "result0671_12.nsv", "result0671_13.nsv", "result0671_14.nsv", "result0671_15.nsv", "result0671_16.nsv", "result0671_17.nsv", "result0671_18.nsv", "result0671_19.nsv"];
val thyn = "vfmTestDefs0671";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
