Theory vfmTest0070[no_sig_docs]
Ancestors vfmTestDefs0070
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0070_0.nsv", "result0070_1.nsv", "result0070_2.nsv", "result0070_3.nsv", "result0070_4.nsv", "result0070_5.nsv", "result0070_6.nsv", "result0070_7.nsv", "result0070_8.nsv", "result0070_9.nsv", "result0070_10.nsv", "result0070_11.nsv"];
val thyn = "vfmTestDefs0070";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
