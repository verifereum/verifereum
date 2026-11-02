Theory vfmTest3017[no_sig_docs]
Ancestors vfmTestDefs3017
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3017_0.nsv", "result3017_1.nsv", "result3017_2.nsv", "result3017_3.nsv", "result3017_4.nsv", "result3017_5.nsv", "result3017_6.nsv", "result3017_7.nsv", "result3017_8.nsv", "result3017_9.nsv", "result3017_10.nsv", "result3017_11.nsv", "result3017_12.nsv", "result3017_13.nsv", "result3017_14.nsv", "result3017_15.nsv"];
val thyn = "vfmTestDefs3017";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
