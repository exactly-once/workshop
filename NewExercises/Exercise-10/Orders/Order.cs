﻿using System.Collections.Generic;
using Messages;

public class Order : Entity
{
    public List<Filling> Items { get; set; }= new List<Filling>();
}