Theory vfmTest0982[no_sig_docs]
Ancestors vfmTestDefs0982
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0982_0.nsv", "result0982_1.nsv", "result0982_2.nsv", "result0982_3.nsv", "result0982_4.nsv", "result0982_5.nsv", "result0982_6.nsv", "result0982_7.nsv", "result0982_8.nsv", "result0982_9.nsv", "result0982_10.nsv", "result0982_11.nsv"];
val thyn = "vfmTestDefs0982";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
