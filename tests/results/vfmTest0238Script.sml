Theory vfmTest0238[no_sig_docs]
Ancestors vfmTestDefs0238
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0238_0.nsv", "result0238_1.nsv", "result0238_2.nsv", "result0238_3.nsv", "result0238_4.nsv", "result0238_5.nsv", "result0238_6.nsv", "result0238_7.nsv", "result0238_8.nsv", "result0238_9.nsv", "result0238_10.nsv", "result0238_11.nsv", "result0238_12.nsv", "result0238_13.nsv", "result0238_14.nsv", "result0238_15.nsv", "result0238_16.nsv", "result0238_17.nsv", "result0238_18.nsv", "result0238_19.nsv", "result0238_20.nsv", "result0238_21.nsv"];
val thyn = "vfmTestDefs0238";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
