Theory vfmTest0406[no_sig_docs]
Ancestors vfmTestDefs0406
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0406_0.nsv", "result0406_1.nsv", "result0406_2.nsv", "result0406_3.nsv", "result0406_4.nsv", "result0406_5.nsv", "result0406_6.nsv", "result0406_7.nsv", "result0406_8.nsv", "result0406_9.nsv", "result0406_10.nsv", "result0406_11.nsv", "result0406_12.nsv", "result0406_13.nsv", "result0406_14.nsv", "result0406_15.nsv"];
val thyn = "vfmTestDefs0406";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
