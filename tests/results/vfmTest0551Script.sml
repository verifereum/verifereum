Theory vfmTest0551[no_sig_docs]
Ancestors vfmTestDefs0551
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0551_0.nsv", "result0551_1.nsv", "result0551_2.nsv", "result0551_3.nsv", "result0551_4.nsv", "result0551_5.nsv", "result0551_6.nsv", "result0551_7.nsv", "result0551_8.nsv", "result0551_9.nsv", "result0551_10.nsv", "result0551_11.nsv", "result0551_12.nsv", "result0551_13.nsv", "result0551_14.nsv", "result0551_15.nsv", "result0551_16.nsv", "result0551_17.nsv", "result0551_18.nsv", "result0551_19.nsv", "result0551_20.nsv", "result0551_21.nsv", "result0551_22.nsv", "result0551_23.nsv"];
val thyn = "vfmTestDefs0551";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
